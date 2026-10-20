import ast
import html
import json
import os
import re
import secrets
import threading
from datetime import datetime
from http import HTTPStatus
from http.cookies import SimpleCookie
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, quote, urlsplit


APP_DIR = Path(__file__).resolve().parent
TEMPLATE_DIR = APP_DIR / "templates"
DATA_FILE = Path(os.environ.get("APPOINTMENTS_FILE", APP_DIR / "appointments.json"))
CLINIC_PHONE = "09815509921"
STAFF_USERNAME = os.environ.get("STAFF_USERNAME", "@Lindy123")
STAFF_PASSWORD = os.environ.get("STAFF_PASSWORD", "@Lindy_1234")
HOST = os.environ.get("HOST", "127.0.0.1")
PORT = int(os.environ.get("PORT", "8000"))
MAX_REQUEST_BYTES = 64 * 1024

_data_lock = threading.RLock()
_sessions_lock = threading.RLock()
_sessions = {}
_template_token = re.compile(r"({{.*?}}|{%.*?%})", re.DOTALL)
_url_for_pattern = re.compile(r"url_for\((.*?)\)")


class SafeHTML(str):
    pass


def _load_appointments():
    with _data_lock:
        try:
            with DATA_FILE.open("r", encoding="utf-8") as data_file:
                appointments = json.load(data_file)
        except FileNotFoundError:
            return []
        except json.JSONDecodeError as error:
            raise ValueError(f"Appointment data file is invalid: {DATA_FILE}") from error
        if not isinstance(appointments, list) or any(
            not isinstance(appointment, dict) for appointment in appointments
        ):
            raise ValueError(f"Appointment data file has an invalid format: {DATA_FILE}")
        return appointments


def _save_appointments(appointments):
    DATA_FILE.parent.mkdir(parents=True, exist_ok=True)
    temporary_file = DATA_FILE.with_name(f".{DATA_FILE.name}.{secrets.token_hex(8)}.tmp")
    with _data_lock:
        try:
            with temporary_file.open("w", encoding="utf-8", newline="\n") as data_file:
                json.dump(appointments, data_file, ensure_ascii=False, indent=2)
                data_file.write("\n")
            os.replace(temporary_file, DATA_FILE)
        finally:
            if temporary_file.exists():
                temporary_file.unlink()


def _next_reference(appointments):
    reference_date = datetime.now().strftime("%Y%m%d")
    existing_references = {
        appointment.get("reference_no") for appointment in appointments
    }
    sequence = len(appointments) + 1001
    reference = f"APT-{reference_date}-{sequence}"
    while reference in existing_references:
        sequence += 1
        reference = f"APT-{reference_date}-{sequence}"
    return reference


def _evaluate_expression(expression, context):
    expression = expression.strip()
    expression = re.sub(r"\bnone\b", "None", expression)
    expression = re.sub(r"\btrue\b", "True", expression)
    expression = re.sub(r"\bfalse\b", "False", expression)
    try:
        tree = ast.parse(expression, mode="eval")
    except SyntaxError as error:
        raise ValueError(f"Unsupported template expression: {expression}") from error

    def evaluate(node):
        if isinstance(node, ast.Constant):
            return node.value
        if isinstance(node, ast.Name):
            if node.id in context:
                return context[node.id]
            raise ValueError(f"Unknown template value: {node.id}")
        if isinstance(node, ast.Attribute):
            owner = evaluate(node.value)
            if isinstance(owner, dict):
                return owner.get(node.attr)
            raise ValueError(f"Unsupported template attribute: {node.attr}")
        if isinstance(node, ast.BoolOp):
            if isinstance(node.op, ast.And):
                result = True
                for value_node in node.values:
                    result = evaluate(value_node)
                    if not result:
                        return result
                return result
            if isinstance(node.op, ast.Or):
                result = False
                for value_node in node.values:
                    result = evaluate(value_node)
                    if result:
                        return result
                return result
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
            return not evaluate(node.operand)
        if isinstance(node, ast.Compare):
            left = evaluate(node.left)
            for operator, comparator in zip(node.ops, node.comparators):
                right = evaluate(comparator)
                if isinstance(operator, ast.Eq):
                    valid = left == right
                elif isinstance(operator, ast.NotEq):
                    valid = left != right
                elif isinstance(operator, ast.Is):
                    valid = left is right
                elif isinstance(operator, ast.IsNot):
                    valid = left is not right
                else:
                    raise ValueError(f"Unsupported template comparison: {expression}")
                if not valid:
                    return False
                left = right
            return True
        if isinstance(node, ast.IfExp):
            return evaluate(node.body) if evaluate(node.test) else evaluate(node.orelse)
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            if node.func.id == "url_for":
                route_names = {
                    "home": "/",
                    "about": "/about",
                    "doctors": "/doctors",
                    "book": "/book",
                    "status": "/status",
                    "admin": "/admin",
                    "logout": "/logout",
                }
                route = evaluate(node.args[0])
                if route not in route_names:
                    raise ValueError(f"Unknown route in template: {route}")
                target = route_names[route]
                parameters = {
                    keyword.arg: evaluate(keyword.value)
                    for keyword in node.keywords
                }
                if parameters:
                    target += "?" + "&".join(
                        f"{quote(str(key))}={quote(str(value))}"
                        for key, value in parameters.items()
                    )
                return target
            if node.func.id == "get_flashed_messages":
                getter = context.get("get_flashed_messages")
                if getter is None:
                    raise ValueError("Flash messages are unavailable")
                with_categories = any(
                    keyword.arg == "with_categories"
                    and evaluate(keyword.value)
                    for keyword in node.keywords
                )
                return getter(with_categories=with_categories)
        raise ValueError(f"Unsupported template expression: {expression}")

    return evaluate(tree.body)


def _parse_nodes(tokens, index=0, stop_tags=()):
    nodes = []
    while index < len(tokens):
        token = tokens[index]
        index += 1
        if token.startswith("{{"):
            nodes.append(("expression", token[2:-2].strip()))
            continue
        if not token.startswith("{%"):
            nodes.append(("text", token))
            continue

        tag = token[2:-2].strip()
        keyword = tag.split(maxsplit=1)[0]
        if keyword in stop_tags:
            return nodes, index, tag
        if keyword == "if":
            branches = []
            condition = tag[3:].strip()
            while True:
                body, index, ending = _parse_nodes(
                    tokens, index, ("elif", "else", "endif")
                )
                branches.append((condition, body))
                if ending.startswith("elif "):
                    condition = ending[5:].strip()
                    continue
                fallback = []
                if ending == "else":
                    fallback, index, ending = _parse_nodes(tokens, index, ("endif",))
                if ending != "endif":
                    raise ValueError("Unclosed if statement in template")
                nodes.append(("if", branches, fallback))
                break
            continue
        if keyword == "for":
            match = re.fullmatch(r"for\s+(.+?)\s+in\s+(.+)", tag)
            if not match:
                raise ValueError(f"Invalid for statement in template: {tag}")
            variables = [name.strip() for name in match.group(1).split(",")]
            body, index, ending = _parse_nodes(tokens, index, ("else", "endfor"))
            fallback = []
            if ending == "else":
                fallback, index, ending = _parse_nodes(tokens, index, ("endfor",))
            if ending != "endfor":
                raise ValueError("Unclosed for statement in template")
            nodes.append(("for", variables, match.group(2).strip(), body, fallback))
            continue
        if keyword == "with":
            match = re.fullmatch(r"with\s+(\w+)\s*=\s*(.+)", tag)
            if not match:
                raise ValueError(f"Invalid with statement in template: {tag}")
            body, index, ending = _parse_nodes(tokens, index, ("endwith",))
            if ending != "endwith":
                raise ValueError("Unclosed with statement in template")
            nodes.append(("with", match.group(1), match.group(2), body))
            continue
        raise ValueError(f"Unsupported template statement: {tag}")
    return nodes, index, ""


def _render_nodes(nodes, context):
    rendered = []
    for node in nodes:
        kind = node[0]
        if kind == "text":
            rendered.append(node[1])
        elif kind == "expression":
            value = _evaluate_expression(node[1], context)
            if value is not None:
                rendered.append(
                    str(value) if isinstance(value, SafeHTML) else html.escape(str(value))
                )
        elif kind == "if":
            for condition, body in node[1]:
                if _evaluate_expression(condition, context):
                    rendered.append(_render_nodes(body, context))
                    break
            else:
                rendered.append(_render_nodes(node[2], context))
        elif kind == "for":
            variables, iterable_expression, body, fallback = node[1:]
            values = _evaluate_expression(iterable_expression, context)
            values = list(values or [])
            if not values:
                rendered.append(_render_nodes(fallback, context))
            for value in values:
                loop_context = dict(context)
                unpacked = value if isinstance(value, tuple) else (value,)
                if len(unpacked) != len(variables):
                    raise ValueError("Template loop values do not match loop variables")
                loop_context.update(zip(variables, unpacked))
                rendered.append(_render_nodes(body, loop_context))
        elif kind == "with":
            local_context = dict(context)
            local_context[node[1]] = _evaluate_expression(node[2], context)
            rendered.append(_render_nodes(node[3], local_context))
    return "".join(rendered)


def _render_template(template_name, context):
    child_path = TEMPLATE_DIR / template_name
    child = child_path.read_text(encoding="utf-8")
    block_match = re.search(
        r"{%\s*block\s+content\s*%}(.*?){%\s*endblock\s*%}",
        child,
        re.DOTALL,
    )
    if block_match:
        child_content = block_match.group(1)
        tokens = _template_token.split(child_content)
        child_nodes, _, _ = _parse_nodes(tokens)
        context = dict(context)
        context["content"] = SafeHTML(_render_nodes(child_nodes, context))
    else:
        context = dict(context)
        context["content"] = SafeHTML(child)

    base = (TEMPLATE_DIR / "base.html").read_text(encoding="utf-8")
    base = re.sub(
        r"{%\s*block\s+content\s*%}.*?{%\s*endblock\s*%}",
        "{{ content }}",
        base,
        count=1,
        flags=re.DOTALL,
    )
    tokens = _template_token.split(base)
    base_nodes, _, _ = _parse_nodes(tokens)
    return _render_nodes(base_nodes, context)


class PharmacyRequestHandler(BaseHTTPRequestHandler):
    server_version = "LindysPharmacy/1.0"

    def _session(self):
        cookies = SimpleCookie()
        cookies.load(self.headers.get("Cookie", ""))
        session_cookie = cookies.get("session_id")
        session_id = session_cookie.value if session_cookie else ""
        with _sessions_lock:
            if session_id not in _sessions:
                session_id = secrets.token_urlsafe(32)
                _sessions[session_id] = {"messages": []}
            session_data = _sessions[session_id]
        return session_id, session_data

    def _send_html(self, content, status=HTTPStatus.OK, session_id=None):
        body = content.encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Referrer-Policy", "same-origin")
        if session_id is not None:
            self.send_header(
                "Set-Cookie",
                f"session_id={session_id}; Path=/; HttpOnly; SameSite=Lax",
            )
        self.end_headers()
        self.wfile.write(body)

    def _redirect(self, location, session_id):
        self.send_response(HTTPStatus.SEE_OTHER)
        self.send_header("Location", location)
        self.send_header("Content-Length", "0")
        self.send_header(
            "Set-Cookie",
            f"session_id={session_id}; Path=/; HttpOnly; SameSite=Lax",
        )
        self.end_headers()

    def _flash(self, session_data, message, category="error"):
        session_data.setdefault("messages", []).append((category, message))

    def _render(self, template_name, session_id, session_data, **context):
        def get_flashed_messages(with_categories=False):
            messages = session_data.pop("messages", [])
            if with_categories:
                return messages
            return [message for _, message in messages]

        page_context = {
            **context,
            "session": session_data,
            "get_flashed_messages": get_flashed_messages,
        }
        content = _render_template(template_name, page_context)
        self._send_html(content, session_id=session_id)

    def _form_data(self):
        try:
            content_length = int(self.headers.get("Content-Length", "0"))
        except ValueError:
            raise ValueError("Invalid request body length")
        if content_length < 0 or content_length > MAX_REQUEST_BYTES:
            raise ValueError("Request body is too large")
        raw_body = self.rfile.read(content_length).decode("utf-8")
        return {
            key: values[0]
            for key, values in parse_qs(raw_body, keep_blank_values=True).items()
        }

    def _home(self, session_id, session_data):
        self._render("index.html", session_id, session_data)

    def _book(self, session_id, session_data, form=None):
        if form is None:
            self._render("book.html", session_id, session_data)
            return

        patient_name = form.get("patient_name", "").strip()
        patient_phone = form.get("patient_phone", "").strip()
        try:
            patient_age = int(form.get("patient_age", ""))
        except ValueError:
            self._flash(session_data, "Please enter a valid age between 0 and 120.")
            self._redirect("/book", session_id)
            return
        if not patient_name or not patient_phone:
            self._flash(session_data, "Please enter your name and phone number.")
            self._redirect("/book", session_id)
            return
        if not 0 <= patient_age <= 120:
            self._flash(session_data, "Please enter a valid age between 0 and 120.")
            self._redirect("/book", session_id)
            return
        patient_address = form.get("patient_address", "").strip()
        patient_gender = form.get("patient_gender", "").strip()
        marital_status = form.get("marital_status", "")
        if not patient_address or not patient_gender:
            self._flash(session_data, "Please enter your address and gender.")
            self._redirect("/book", session_id)
            return
        if marital_status not in ("Single", "Married", "Widowed"):
            self._flash(session_data, "Please select a valid marital status.")
            self._redirect("/book", session_id)
            return
        service = form.get("service", "")
        if not service:
            self._flash(session_data, "Please select a service.")
            self._redirect("/book", session_id)
            return
        if service == "Others:":
            other_service = form.get("other_service", "").strip()
            if not other_service:
                self._flash(session_data, "Please specify the other service you need.")
                self._redirect("/book", session_id)
                return
            service = f"Others: {other_service}"

        with _data_lock:
            appointments = _load_appointments()
            appointment_id = max(
                (int(appointment.get("id", 0)) for appointment in appointments),
                default=0,
            ) + 1
            reference = _next_reference(appointments)
            appointments.append(
                {
                    "id": appointment_id,
                    "reference_no": reference,
                    "patient_name": patient_name,
                    "patient_phone": patient_phone,
                    "patient_age": patient_age,
                    "patient_address": patient_address,
                    "patient_gender": patient_gender,
                    "marital_status": marital_status,
                    "appointment_date": "",
                    "appointment_time": "",
                    "service": service,
                    "notes": form.get("notes", ""),
                    "status": "Pending",
                    "created_at": datetime.now().isoformat(timespec="seconds"),
                    "doctor_name": "",
                }
            )
            _save_appointments(appointments)

        self._flash(
            session_data,
            f"Appointment requested successfully! Your Reference Code is {reference}",
            "success",
        )
        self._redirect(f"/status?ref={quote(reference)}", session_id)

    def _status(self, session_id, session_data, query):
        reference = query.get("ref", [""])[0].strip()
        appointment = None
        if reference:
            appointment = next(
                (
                    item
                    for item in _load_appointments()
                    if item.get("reference_no") == reference
                ),
                None,
            )
            if appointment is None:
                self._flash(
                    session_data,
                    "No appointment found with that Reference Code.",
                )
        self._render(
            "status.html",
            session_id,
            session_data,
            appointment=appointment,
            ref=reference,
            clinic_phone=CLINIC_PHONE,
        )

    def _admin(self, session_id, session_data, form=None):
        if not session_data.get("staff_logged_in"):
            if form is not None and "username" in form:
                if (
                    form.get("username", "").strip() == STAFF_USERNAME
                    and form.get("password", "") == STAFF_PASSWORD
                ):
                    session_data["staff_logged_in"] = True
                    self._flash(session_data, "Login successful.", "success")
                    self._redirect("/admin", session_id)
                    return
                self._flash(session_data, "Invalid username or password.")
            self._render(
                "admin.html",
                session_id,
                session_data,
                login_required=True,
            )
            return

        if form is not None:
            appointment_id = form.get("appointment_id", "")
            new_status = form.get("status", "")
            with _data_lock:
                appointments = _load_appointments()
                appointment = next(
                    (
                        item
                        for item in appointments
                        if str(item.get("id")) == appointment_id
                    ),
                    None,
                )
                if appointment is None:
                    self._flash(session_data, "Appointment not found.")
                elif new_status == "Remove":
                    appointments.remove(appointment)
                    _save_appointments(appointments)
                    self._flash(session_data, "Appointment removed.", "success")
                elif new_status not in ("Approved", "Cancelled", "Pending"):
                    self._flash(session_data, "Choose a valid appointment action.")
                elif appointment.get("status") == new_status:
                    self._flash(
                        session_data,
                        f"Appointment is already {new_status.lower()}.",
                        "success",
                    )
                else:
                    appointment["status"] = new_status
                    _save_appointments(appointments)
                    messages = {
                        "Approved": "Appointment approved.",
                        "Pending": "Appointment set to pending.",
                        "Cancelled": "Appointment cancelled.",
                    }
                    self._flash(session_data, messages[new_status], "success")
            self._redirect("/admin", session_id)
            return

        appointments = sorted(
            _load_appointments(),
            key=lambda appointment: appointment.get("created_at", ""),
            reverse=True,
        )
        self._render(
            "admin.html",
            session_id,
            session_data,
            appointments=appointments,
            appointment_count=len(appointments),
            login_required=False,
        )

    def do_GET(self):
        session_id, session_data = self._session()
        parsed_url = urlsplit(self.path)
        path = parsed_url.path
        query = parse_qs(parsed_url.query, keep_blank_values=True)
        try:
            if path == "/":
                self._home(session_id, session_data)
            elif path == "/about":
                self._render("about.html", session_id, session_data)
            elif path == "/doctors":
                self._render("doctors.html", session_id, session_data)
            elif path == "/book":
                self._book(session_id, session_data)
            elif path == "/status":
                self._status(session_id, session_data, query)
            elif path == "/admin":
                self._admin(session_id, session_data)
            elif path == "/logout":
                session_data.pop("staff_logged_in", None)
                self._flash(session_data, "You have been logged out.", "success")
                self._redirect("/admin", session_id)
            else:
                self.send_error(HTTPStatus.NOT_FOUND)
        except (OSError, ValueError, TypeError) as error:
            self.log_error("Request failed: %s", error)
            self.send_error(HTTPStatus.INTERNAL_SERVER_ERROR)

    def do_POST(self):
        session_id, session_data = self._session()
        path = urlsplit(self.path).path
        try:
            form = self._form_data()
            if path == "/book":
                self._book(session_id, session_data, form)
            elif path == "/admin":
                self._admin(session_id, session_data, form)
            else:
                self.send_error(HTTPStatus.NOT_FOUND)
        except (OSError, ValueError, TypeError) as error:
            self.log_error("Request failed: %s", error)
            self.send_error(HTTPStatus.INTERNAL_SERVER_ERROR)

    def log_message(self, format_string, *args):
        super().log_message(format_string, *args)


def main():
    server = ThreadingHTTPServer((HOST, PORT), PharmacyRequestHandler)
    print(f"Lindy's Pharmacy website is running at http://{HOST}:{PORT}")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nShutting down Lindy's Pharmacy website.")
    finally:
        server.server_close()


if __name__ == "__main__":
    main()
