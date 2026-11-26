import io
import json
import os
import queue
import sqlite3
import threading
import time
from datetime import date, datetime, timedelta

import cv2
from flask import Flask, Response, jsonify, redirect, render_template_string, request, url_for
from pyzbar.pyzbar import decode, ZBarSymbol

# Raspberry Pi: Picamera2 is used when available.
# Windows/Linux development: OpenCV webcam fallback is used.
try:
    from picamera2 import Picamera2
    HAS_PICAMERA2 = True
except ImportError:
    Picamera2 = None
    HAS_PICAMERA2 = False

APP = Flask(__name__)
DB_PATH = os.environ.get("MESS_DB", "smart_mess.db")
PORT = int(os.environ.get("PORT", "8000"))

INITIAL_DEPOSIT = 21000
PACKAGE_DAYS = 150
MEAL_PRICES = {
    "Breakfast": 30,
    "Lunch": 50,
    "Snacks": 20,
    "Dinner": 40,
}

# Change these default time windows to match your mess schedule.
# Format: start inclusive, end exclusive, 24-hour HH:MM.
DEFAULT_MEAL_WINDOWS = {
    "Breakfast": ("06:00", "10:00"),
    "Lunch": ("11:00", "15:00"),
    "Snacks": ("16:00", "18:00"),
    "Dinner": ("19:00", "22:00"),
}

BARCODE_TYPES = [
    ZBarSymbol.CODE128, ZBarSymbol.CODE39, ZBarSymbol.EAN13,
    ZBarSymbol.EAN8, ZBarSymbol.UPCA, ZBarSymbol.UPCE,
    ZBarSymbol.I25, ZBarSymbol.CODABAR,
]

camera_lock = threading.Lock()
barcode_lock = threading.Lock()
latest_barcode = None
latest_barcode_time = 0.0
last_processed = {}
camera = None
camera_kind = None
camera_started = False
last_decode_time = 0.0
DECODE_INTERVAL = 0.20

# A barcode that stays in front of the camera keeps decoding on every frame.
# Once a barcode is handled, the same barcode is ignored for this many seconds,
# so one card means exactly one charge, one beep and one stable screen state.
# A different student (different barcode) is never held back by this window.
RESCAN_SECONDS = 30.0

# Safety net on top of the rescan window: an identical alert for the same
# barcode is not repeated within this window.
ALERT_BUFFER_SECONDS = 30.0
alert_lock = threading.Lock()
alert_state = {"id": 0, "barcode": None, "time": 0.0, "message": ""}

# Last completed scan, kept separate from the per-frame preview state so the
# result cannot be overwritten by the next video frame.
last_scan = {"barcode": None, "result": None, "alert": None, "detected_at": None, "at": 0.0}

# Server-Sent Events: every completed scan is pushed to open pages, so the
# scanner and the transaction list update without polling or a refresh.
subscribers = []
subscribers_lock = threading.Lock()

def publish(event):
    payload = json.dumps(event)
    with subscribers_lock:
        for sub in list(subscribers):
            try:
                sub.put_nowait(payload)
            except queue.Full:
                # Slow client: drop its oldest message rather than blocking scans.
                try:
                    sub.get_nowait()
                except queue.Empty:
                    pass
                try:
                    sub.put_nowait(payload)
                except queue.Full:
                    pass

def db():
    conn = sqlite3.connect(DB_PATH, timeout=10)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA foreign_keys = ON")
    conn.execute("PRAGMA journal_mode = WAL")
    return conn

def init_db():
    with db() as con:
        con.executescript("""
        CREATE TABLE IF NOT EXISTS students (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            student_code TEXT NOT NULL UNIQUE,
            name TEXT NOT NULL,
            department TEXT NOT NULL,
            year TEXT NOT NULL,
            barcode TEXT NOT NULL UNIQUE,
            balance INTEGER NOT NULL DEFAULT 0,
            package_start TEXT NOT NULL,
            package_end TEXT NOT NULL,
            created_at TEXT NOT NULL
        );

        CREATE TABLE IF NOT EXISTS transactions (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            student_id INTEGER NOT NULL,
            meal_date TEXT NOT NULL,
            meal_type TEXT NOT NULL,
            amount INTEGER NOT NULL,
            balance_after INTEGER NOT NULL,
            barcode TEXT NOT NULL,
            created_at TEXT NOT NULL,
            UNIQUE(student_id, meal_date, meal_type),
            FOREIGN KEY(student_id) REFERENCES students(id)
        );

        CREATE TABLE IF NOT EXISTS deposits (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            student_id INTEGER NOT NULL,
            amount INTEGER NOT NULL,
            note TEXT NOT NULL,
            created_at TEXT NOT NULL,
            FOREIGN KEY(student_id) REFERENCES students(id)
        );

        CREATE TABLE IF NOT EXISTS meal_windows (
            meal_type TEXT PRIMARY KEY,
            start_time TEXT NOT NULL,
            end_time TEXT NOT NULL
        );
        """)

        for meal, (start, end) in DEFAULT_MEAL_WINDOWS.items():
            con.execute(
                "INSERT OR IGNORE INTO meal_windows(meal_type,start_time,end_time) VALUES(?,?,?)",
                (meal, start, end)
            )

        count = con.execute("SELECT COUNT(*) FROM students").fetchone()[0]
        if count == 0:
            today = date.today()
            start = today.isoformat()
            end = (today + timedelta(days=PACKAGE_DAYS - 1)).isoformat()
            demo_names = [
                ("Aarav Kumar", "CSE", "2nd Year"),
                ("Ananya Reddy", "ECE", "2nd Year"),
                ("Sai Teja", "EEE", "3rd Year"),
                ("Priya Sharma", "CSE", "1st Year"),
                ("Rahul Varma", "MECH", "3rd Year"),
                ("Kavya Rao", "CIVIL", "2nd Year"),
                ("Vikram Naidu", "CSE", "4th Year"),
                ("Sneha Patel", "ECE", "1st Year"),
                ("Rohit Kumar", "IT", "3rd Year"),
                ("Divya Sri", "CSE", "2nd Year"),
                ("Arjun Reddy", "EEE", "2nd Year"),
                ("Pooja Singh", "IT", "1st Year"),
                ("Manoj Babu", "MECH", "4th Year"),
                ("Keerthi Devi", "CSE", "3rd Year"),
                ("Nikhil Varma", "ECE", "2nd Year"),
                ("Harika Reddy", "CIVIL", "1st Year"),
                ("Kiran Kumar", "IT", "4th Year"),
                ("Meghana Rao", "CSE", "1st Year"),
                ("Sandeep Yadav", "EEE", "3rd Year"),
                ("Lakshmi Priya", "ECE", "4th Year"),
            ]
            for i, (name, dept, year) in enumerate(demo_names, start=1):
                code = f"STU{i:04d}"
                barcode = f"MESS{i:06d}"
                cur = con.execute("""
                    INSERT INTO students
                    (student_code,name,department,year,barcode,balance,package_start,package_end,created_at)
                    VALUES(?,?,?,?,?,?,?,?,?)
                """, (code, name, dept, year, barcode, INITIAL_DEPOSIT, start, end,
                      datetime.now().isoformat(timespec="seconds")))
                con.execute(
                    "INSERT INTO deposits(student_id,amount,note,created_at) VALUES(?,?,?,?)",
                    (cur.lastrowid, INITIAL_DEPOSIT, "Initial 150-day demo package",
                     datetime.now().isoformat(timespec="seconds"))
                )

def get_active_meal(now=None):
    now = now or datetime.now()
    current = now.strftime("%H:%M")
    with db() as con:
        windows = con.execute("SELECT * FROM meal_windows").fetchall()
    for row in windows:
        # Supports ordinary same-day windows (all defaults are same-day).
        if row["start_time"] <= current < row["end_time"]:
            return row["meal_type"]
    return None

def process_meal_scan(barcode):
    """Atomically identify student, prevent duplicates, and debit the wallet."""
    now = datetime.now()
    meal = get_active_meal(now)
    if meal is None:
        return {"status": "outside_meal_time", "message": "No meal is currently active."}

    price = MEAL_PRICES[meal]
    today = date.today().isoformat()
    stamp = now.isoformat(timespec="seconds")

    con = db()
    try:
        con.execute("BEGIN IMMEDIATE")
        student = con.execute("SELECT * FROM students WHERE barcode = ?", (barcode,)).fetchone()
        if student is None:
            con.rollback()
            return {"status": "unknown_student", "message": "Barcode is not registered."}

        duplicate = con.execute("""
            SELECT id FROM transactions
            WHERE student_id = ? AND meal_date = ? AND meal_type = ?
        """, (student["id"], today, meal)).fetchone()
        if duplicate:
            con.rollback()
            return {
                "status": "duplicate",
                "message": f"{meal} already claimed today.",
                "student": student["name"],
                "meal": meal,
                "balance": student["balance"],
            }

        # Negative balances are allowed by the selected project rule.
        new_balance = student["balance"] - price
        con.execute("UPDATE students SET balance = ? WHERE id = ?",
                    (new_balance, student["id"]))
        con.execute("""
            INSERT INTO transactions
            (student_id,meal_date,meal_type,amount,balance_after,barcode,created_at)
            VALUES(?,?,?,?,?,?,?)
        """, (student["id"], today, meal, price, new_balance, barcode, stamp))
        con.commit()
        return {
            "status": "success",
            "message": f"{meal} charged: Rs. {price}",
            "student": student["name"],
            "student_code": student["student_code"],
            "meal": meal,
            "amount": price,
            "balance": new_balance,
            "time": now.strftime("%H:%M:%S"),
            "meal_date": today,
            "created_at": stamp,
        }
    except sqlite3.IntegrityError:
        con.rollback()
        return {"status": "duplicate", "message": "This meal was already claimed today."}
    finally:
        con.close()

def alert_message(result, reasons):
    parts = []
    if result.get("student"):
        parts.append(str(result["student"]))
    if "duplicate" in reasons:
        parts.append("Duplicate scan - this meal was already claimed today")
    if "zero_or_negative_balance" in reasons:
        balance = result.get("balance")
        try:
            parts.append(f"Wallet balance is {int(balance):,} (zero or negative)")
        except (TypeError, ValueError):
            parts.append("Wallet balance is zero or negative")
    return " - ".join(parts)

def register_alert(barcode_value, result):
    """Flag a scan that needs a beep + red UI.

    The buffer is per barcode: the same card re-read inside
    ALERT_BUFFER_SECONDS stays silent, while a different student arriving with
    a duplicate entry always alerts.
    """
    if not result:
        return None

    reasons = []
    if result.get("status") == "duplicate":
        reasons.append("duplicate")
    balance = result.get("balance")
    if isinstance(balance, (int, float)) and balance <= 0:
        reasons.append("zero_or_negative_balance")
    if not reasons:
        return None

    now = time.time()
    with alert_lock:
        if (alert_state["barcode"] == barcode_value
                and now - alert_state["time"] < ALERT_BUFFER_SECONDS):
            alert_state["time"] = now
            return None
        alert_state["id"] += 1
        alert_state["barcode"] = barcode_value
        alert_state["time"] = now
        alert_state["message"] = alert_message(result, reasons)
        return {
            "id": alert_state["id"],
            "message": alert_state["message"],
            "reasons": reasons,
        }

def handle_detected_barcode(value):
    global latest_barcode, latest_barcode_time, last_scan
    now = time.time()
    with barcode_lock:
        latest_barcode = {"data": value, "type": "BARCODE"}
        latest_barcode_time = now
        previous = last_processed.get(value, 0)
        # One card, one charge: ignore this barcode for RESCAN_SECONDS after it
        # has been handled. Other barcodes are processed immediately.
        should_process = now - previous >= RESCAN_SECONDS
        if should_process:
            last_processed[value] = now
            if len(last_processed) > 500:
                for old in [k for k, t in last_processed.items() if now - t > 300]:
                    last_processed.pop(old, None)
    if not should_process:
        return

    result = process_meal_scan(value)
    alert = register_alert(value, result)
    detected_at = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    event = {"type": "scan", "barcode": value, "result": result, "detected_at": detected_at}
    if alert:
        event["alert"] = alert
    if result.get("status") == "success":
        event["tx"] = {
            "meal_date": result.get("meal_date"),
            "created_at": result.get("created_at"),
            "name": result.get("student"),
            "student_code": result.get("student_code"),
            "meal_type": result.get("meal"),
            "amount": result.get("amount"),
            "balance_after": result.get("balance"),
        }

    with barcode_lock:
        latest_barcode["result"] = result
        latest_barcode["detected_at"] = detected_at
        last_scan = {"barcode": value, "result": result, "alert": alert,
                     "detected_at": detected_at, "at": now}

    publish(event)
    if alert:
        print("ALERT:", alert["message"])
    print("SCAN:", value, result)

def start_camera():
    global camera, camera_kind, camera_started
    if camera_started:
        return
    if HAS_PICAMERA2:
        camera = Picamera2()
        config = camera.create_video_configuration(
            main={"size": (1280, 960), "format": "RGB888"},
            controls={"AwbEnable": True, "AeEnable": True, "Contrast": 1.1, "Sharpness": 1.2},
            buffer_count=4,
        )
        camera.configure(config)
        camera.start()
        time.sleep(2)
        camera_kind = "picamera2"
    else:
        camera = cv2.VideoCapture(0)
        camera.set(cv2.CAP_PROP_FRAME_WIDTH, 1280)
        camera.set(cv2.CAP_PROP_FRAME_HEIGHT, 720)
        if not camera.isOpened():
            raise RuntimeError("Could not open camera. Connect a webcam or run on Raspberry Pi.")
        camera_kind = "opencv"
    camera_started = True

def capture_frame():
    with camera_lock:
        if camera_kind == "picamera2":
            frame = camera.capture_array("main")
            return cv2.cvtColor(frame, cv2.COLOR_RGB2BGR)
        ok, frame = camera.read()
        return frame if ok else None

def generate_frames():
    global last_decode_time
    while True:
        frame = capture_frame()
        if frame is None:
            time.sleep(0.05)
            continue

        now = time.time()
        if now - last_decode_time >= DECODE_INTERVAL:
            last_decode_time = now
            gray = cv2.cvtColor(frame, cv2.COLOR_BGR2GRAY)
            try:
                found = decode(gray, symbols=BARCODE_TYPES)
            except Exception as exc:
                print("Barcode decode error:", exc)
                found = []
            for item in found:
                value = item.data.decode("utf-8", errors="replace").strip()
                if not value:
                    continue
                handle_detected_barcode(value)
                x, y, w, h = item.rect
                cv2.rectangle(frame, (x, y), (x+w, y+h), (0, 0, 0), 3)
                cv2.putText(frame, value[:80], (x, max(25, y-8)),
                            cv2.FONT_HERSHEY_SIMPLEX, 0.7, (0, 0, 0), 2)

        ok, encoded = cv2.imencode(".jpg", frame, [cv2.IMWRITE_JPEG_QUALITY, 82])
        if not ok:
            continue
        yield b"--frame\r\nContent-Type: image/jpeg\r\n\r\n" + encoded.tobytes() + b"\r\n"

def money(value):
    return f"₹{int(value):,}"

BASE_STYLE = """
<style>
*{box-sizing:border-box}
body{font-family:-apple-system,"Segoe UI",Roboto,Arial,sans-serif;margin:0;background:#f7f7f8;color:#16181d}
header{background:#fff;padding:14px 24px;border-bottom:1px solid #e3e4e8;display:flex;gap:24px;align-items:center;flex-wrap:wrap}
header strong{font-size:15px;font-weight:700;letter-spacing:.14em;text-transform:uppercase}
nav{display:flex;gap:20px;flex-wrap:wrap;font-size:14px;margin-left:auto}
nav a{color:#4a4f59;padding:4px 0;border-bottom:2px solid transparent}nav a:hover{color:#16181d;border-bottom-color:#16181d;text-decoration:none}
main{max-width:1180px;margin:26px auto;padding:0 20px}
h1{font-size:21px;font-weight:600;margin:0 0 4px;letter-spacing:-.01em}
h2{font-size:12px;font-weight:600;margin:0 0 12px;letter-spacing:.08em;text-transform:uppercase;color:#7a7e87}
.muted{color:#7a7e87;font-size:13px}.grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(180px,1fr));gap:12px}
.stat,.panel{background:#fff;border:1px solid #e3e4e8;border-radius:6px;padding:16px}
.stat small{display:block;color:#7a7e87;font-size:11px;letter-spacing:.06em;text-transform:uppercase;margin-bottom:10px}
.stat strong{font-size:22px;font-weight:600}
table{width:100%;border-collapse:collapse;font-size:14px}
th,td{text-align:left;padding:10px;border-bottom:1px solid #eef0f3}
th{font-weight:600;font-size:11px;letter-spacing:.07em;text-transform:uppercase;color:#7a7e87;border-bottom:1px solid #e3e4e8}
tbody tr:last-child td{border-bottom:none}
input,button,select{font:inherit;padding:8px 10px;border:1px solid #cfd2d8;border-radius:4px;background:#fff;color:#16181d}
button{cursor:pointer;font-weight:500}button:hover{background:#f2f3f5}
a{color:#16181d;text-decoration:none}
.actions{display:flex;gap:8px;flex-wrap:wrap}
.notice{padding:12px;border:1px solid #e3e4e8;border-radius:6px;background:#fff;margin:12px 0;font-size:14px}
.good{border-left:3px solid #2e7d32}.bad{border-left:3px solid #8c1d1d}
video,img{max-width:100%}
.scanner{width:100%;display:block;border-radius:4px;background:#000;max-height:380px;object-fit:cover}
form.inline{display:inline-flex;gap:6px;align-items:center}
.pill{display:inline-block;padding:2px 9px;border-radius:999px;font-size:11px;font-weight:600;letter-spacing:.04em;text-transform:uppercase;border:1px solid transparent}
.pill-ok{background:#eaf6ec;color:#1b5e20;border-color:#bfe0c4}
.pill-warn{background:#fdecec;color:#8c1d1d;border-color:#f3c6c6}
.pill-neutral{background:#f2f3f5;color:#5c616b;border-color:#e3e4e8}
tr.ok td{background:#f6fbf7}tr.ok td.amount{color:#1b5e20;font-weight:600}
tr.ok td.date{color:#5c616b}
.scan-grid{display:grid;grid-template-columns:minmax(0,1fr) minmax(0,1fr);gap:16px;align-items:start;margin-top:16px}
.cam-panel{position:sticky;top:16px}
.tx-scroll{max-height:560px;overflow:auto}
@media(max-width:900px){.scan-grid{grid-template-columns:1fr}.cam-panel{position:static}}
@media(max-width:600px){header{padding:12px 16px}main{margin:18px auto;padding:0 14px}table{font-size:12px}th,td{padding:8px 6px}}
</style>
"""

def page(title, body):
    return render_template_string("""
    <!doctype html><html><head><meta name="viewport" content="width=device-width,initial-scale=1">
    <title>{{title}} · NIT AP MESS</title>""" + BASE_STYLE + """</head><body>
    <header><strong>NIT AP MESS</strong><nav>
    <a href="/">Dashboard</a><a href="/students">Students</a><a href="/scanner">Scanner</a>
    <a href="/settings">Meal Timings</a>
    </nav></header><main>""" + body + """</main></body></html>
    """, title=title)

@APP.route("/")
def dashboard():
    with db() as con:
        total = con.execute("SELECT COUNT(*) FROM students").fetchone()[0]
        balance = con.execute("SELECT COALESCE(SUM(balance),0) FROM students").fetchone()[0]
        today_count = con.execute("SELECT COUNT(*) FROM transactions WHERE meal_date=?",
                                  (date.today().isoformat(),)).fetchone()[0]
        today_amount = con.execute("SELECT COALESCE(SUM(amount),0) FROM transactions WHERE meal_date=?",
                                   (date.today().isoformat(),)).fetchone()[0]
        recent = con.execute("""
            SELECT t.*,s.name,s.student_code FROM transactions t
            JOIN students s ON s.id=t.student_id ORDER BY t.id DESC LIMIT 8
        """).fetchall()
    body = """
    <h1>Dashboard</h1>
    <section class="grid">
      <div class="stat"><small>Registered students</small><strong>{{total}}</strong></div>
      <div class="stat"><small>Total wallet balance</small><strong>{{balance}}</strong></div>
      <div class="stat"><small>Meals served today</small><strong>{{today_count}}</strong></div>
      <div class="stat"><small>Today's deductions</small><strong>{{today_amount}}</strong></div>
    </section>
    <section class="panel" style="margin-top:18px">
      <h2>Recent meal transactions</h2>
      <table><tr><th>Time</th><th>Student</th><th>Meal</th><th>Amount</th><th>Balance</th></tr>
      {% for t in recent %}<tr class="ok"><td class="date">{{t.created_at[11:19]}}</td><td>{{t.name}} <span class="muted">{{t.student_code}}</span></td>
      <td>{{t.meal_type}}</td><td class="amount">{{money(t.amount)}}</td><td>{{money(t.balance_after)}}</td></tr>
      {% else %}<tr><td colspan="5" class="muted">No transactions yet.</td></tr>{% endfor %}</table>
    </section>
    """
    return page("Dashboard", render_template_string(body, total=total, balance=money(balance),
                today_count=today_count, today_amount=money(today_amount), recent=recent, money=money))

@APP.route("/students")
def students():
    with db() as con:
        rows = con.execute("SELECT * FROM students ORDER BY student_code").fetchall()
    body = """
    <h1>Students</h1><p class="muted">20 demo accounts are preloaded. Demo barcode values are shown for testing.</p>
    <div class="panel"><table><tr><th>ID</th><th>Name</th><th>Department</th><th>Barcode</th><th>Wallet</th><th>Package ends</th><th>Action</th></tr>
    {% for s in rows %}<tr><td>{{s.student_code}}</td><td>{{s.name}}</td><td>{{s.department}}</td>
    <td>{{s.barcode}}</td><td>{{money(s.balance)}}</td><td>{{s.package_end}}</td>
    <td><a href="/student/{{s.id}}">View</a></td></tr>{% endfor %}</table></div>
    """
    return page("Students", render_template_string(body, rows=rows, money=money))

@APP.route("/student/<int:student_id>")
def student_detail(student_id):
    with db() as con:
        s = con.execute("SELECT * FROM students WHERE id=?", (student_id,)).fetchone()
        if not s:
            return "Student not found", 404
        tx = con.execute("SELECT * FROM transactions WHERE student_id=? ORDER BY id DESC LIMIT 30",
                         (student_id,)).fetchall()
        deposits = con.execute("SELECT * FROM deposits WHERE student_id=? ORDER BY id DESC",
                               (student_id,)).fetchall()
    body = """
    <h1>{{s.name}}</h1><p class="muted">{{s.student_code}} · {{s.department}} · {{s.year}} · Barcode: {{s.barcode}}</p>
    <section class="grid">
      <div class="stat"><small>Current wallet balance</small><strong>{{money(s.balance)}}</strong></div>
      <div class="stat"><small>Package start</small><strong style="font-size:17px">{{s.package_start}}</strong></div>
      <div class="stat"><small>Package end</small><strong style="font-size:17px">{{s.package_end}}</strong></div>
    </section>
    <section class="panel" style="margin-top:16px">
      <h2>Add / renew package</h2>
      <p class="muted">Adds ₹21,000 and extends the package by 150 days. Existing wallet balance carries forward.</p>
      <form method="post" action="/student/{{s.id}}/renew"><button type="submit">Add ₹21,000 package</button></form>
    </section>
    <section class="panel" style="margin-top:16px"><h2>Meal transactions</h2>
    <table><tr><th>Date</th><th>Time</th><th>Meal</th><th>Deduction</th><th>Balance after</th></tr>
    {% for t in tx %}<tr><td>{{t.meal_date}}</td><td>{{t.created_at[11:19]}}</td><td>{{t.meal_type}}</td>
    <td>{{money(t.amount)}}</td><td>{{money(t.balance_after)}}</td></tr>{% else %}
    <tr><td colspan="5" class="muted">No meal transactions.</td></tr>{% endfor %}</table></section>
    <section class="panel" style="margin-top:16px"><h2>Deposits</h2>
    <table><tr><th>Date</th><th>Amount</th><th>Note</th></tr>
    {% for d in deposits %}<tr><td>{{d.created_at[:10]}}</td><td>{{money(d.amount)}}</td><td>{{d.note}}</td></tr>{% endfor %}</table></section>
    """
    return page("Student", render_template_string(body, s=s, tx=tx, deposits=deposits, money=money))

@APP.route("/student/<int:student_id>/renew", methods=["POST"])
def renew(student_id):
    today = date.today()
    stamp = datetime.now().isoformat(timespec="seconds")
    with db() as con:
        s = con.execute("SELECT * FROM students WHERE id=?", (student_id,)).fetchone()
        if not s:
            return "Student not found", 404
        old_end = date.fromisoformat(s["package_end"])
        new_start = max(today, old_end + timedelta(days=1))
        new_end = new_start + timedelta(days=PACKAGE_DAYS - 1)
        con.execute("""
            UPDATE students SET balance=balance+?, package_start=?, package_end=? WHERE id=?
        """, (INITIAL_DEPOSIT, new_start.isoformat(), new_end.isoformat(), student_id))
        con.execute("INSERT INTO deposits(student_id,amount,note,created_at) VALUES(?,?,?,?)",
                    (student_id, INITIAL_DEPOSIT, "150-day package renewal; previous balance carried forward", stamp))
    return redirect(url_for("student_detail", student_id=student_id))

@APP.route("/transactions")
def transactions():
    # Transactions now live on the scanner page (old links keep working).
    return redirect(url_for("scanner"))

@APP.route("/settings", methods=["GET", "POST"])
def settings():
    if request.method == "POST":
        with db() as con:
            for meal in MEAL_PRICES:
                start = request.form.get(meal + "_start", "").strip()
                end = request.form.get(meal + "_end", "").strip()
                if start and end:
                    con.execute("UPDATE meal_windows SET start_time=?,end_time=? WHERE meal_type=?",
                                (start, end, meal))
        return redirect(url_for("settings"))
    with db() as con:
        rows = con.execute("SELECT * FROM meal_windows ORDER BY CASE meal_type WHEN 'Breakfast' THEN 1 WHEN 'Lunch' THEN 2 WHEN 'Snacks' THEN 3 ELSE 4 END").fetchall()
    body = """
    <h1>Meal timings</h1><p class="muted">The scanner uses these time windows to choose the meal automatically.</p>
    <form method="post" class="panel"><table><tr><th>Meal</th><th>Start</th><th>End</th><th>Price</th></tr>
    {% for r in rows %}<tr><td>{{r.meal_type}}</td>
    <td><input type="time" name="{{r.meal_type}}_start" value="{{r.start_time}}"></td>
    <td><input type="time" name="{{r.meal_type}}_end" value="{{r.end_time}}"></td>
    <td>{{money(prices[r.meal_type])}}</td></tr>{% endfor %}</table><p><button type="submit">Save meal timings</button></p></form>
    """
    return page("Meal Timings", render_template_string(body, rows=rows, prices=MEAL_PRICES, money=money))

@APP.route("/scanner")
def scanner():
    active = get_active_meal()
    with db() as con:
        rows = con.execute("""
            SELECT t.*,s.name,s.student_code FROM transactions t
            JOIN students s ON s.id=t.student_id ORDER BY t.id DESC LIMIT 200
        """).fetchall()
    body = """
    <h1>Scanner &amp; transactions</h1>
    <p class="muted">Hold a registered student barcode in front of the camera. The active meal is chosen from the current time and the wallet is charged automatically.</p>

    <section class="scan-grid">
      <div>
        <div class="panel" style="margin-bottom:16px">
          <h2>Current meal</h2>
          <p style="margin:0;font-size:18px;font-weight:600">{{active or "No active meal"}}
          {% if active %}<span class="muted" style="font-weight:400">&middot; ₹{{prices[active]}}</span>{% endif %}</p>
          <div id="status-box" class="status"></div>
        </div>
        <div class="panel">
          <h2>Latest scan</h2>
          <div id="scan" class="muted">Waiting for barcode...</div>
        </div>
      </div>
      <div class="panel cam-panel">
        <h2>Camera</h2>
        <img class="scanner" src="/video" alt="Live camera preview">
        <p class="muted" style="margin:10px 0 0">Live preview &middot; barcodes are read automatically</p>
      </div>
    </section>

    <section class="panel" style="margin-top:16px">
      <h2>Recent transactions</h2>
      <div class="tx-scroll"><table>
        <thead><tr><th>Date</th><th>Time</th><th>Student</th><th>Meal</th><th>Deduction</th><th>Balance</th><th>Status</th></tr></thead>
        <tbody id="txbody">
        {% for t in rows %}<tr class="ok"><td class="date">{{t.meal_date}}</td><td class="date">{{t.created_at[11:19]}}</td>
        <td>{{t.name}} <span class="muted">{{t.student_code}}</span></td><td>{{t.meal_type}}</td>
        <td class="amount">{{money(t.amount)}}</td><td>{{money(t.balance_after)}}</td>
        <td><span class="pill pill-ok">Success</span></td></tr>
        {% else %}<tr id="txempty"><td colspan="7" class="muted">No transactions yet.</td></tr>{% endfor %}
        </tbody>
      </table></div>
      <p class="muted" id="txcount" style="margin:10px 0 0">Showing the latest {{rows|length}} transactions.</p>
    </section>

    <style>
    /* Held states: green stays until the next scan, red stays until the next scan. */
    body.ok-mode{background:#eef7f0}
    body.ok-mode .panel{border-color:#bfe0c4}
    body.ok-mode header{border-bottom-color:#bfe0c4}
    .status{display:none;margin-top:14px;padding:12px 14px;border-radius:4px;font-size:15px;font-weight:600}
    .status.ok{display:block;background:#1b5e20;color:#fff}
    .status.alert{display:block;background:#7f0000;color:#fff;animation:alertpulse 1s ease-in-out infinite}
    .status.neutral{display:block;background:#f2f3f5;color:#4a4f59;font-weight:500;border:1px solid #e3e4e8}
    body.alert-mode{background:#b71c1c;color:#fff}
    body.alert-mode header{background:#8e1414;border-bottom-color:rgba(255,255,255,.4)}
    body.alert-mode a,body.alert-mode .muted,body.alert-mode h2{color:#ffe0e0}
    body.alert-mode .panel{background:#c62828;border-color:#ef9a9a}
    body.alert-mode h1{color:#fff}
    body.alert-mode tr.ok td,body.alert-mode tr.ok td.amount{background:#b02020;color:#fff}
    body.alert-mode .pill-ok{background:#ffcdd2;color:#7f0000;border-color:#fff}
    body.alert-mode th{color:#ffcdd2;border-bottom-color:rgba(255,255,255,.35)}
    body.alert-mode td{border-bottom-color:rgba(255,255,255,.18)}
    tr.new td{animation:rowin 1.4s ease-out}
    @keyframes rowin{from{background:#cfe9d4}to{background:#f6fbf7}}
    @keyframes alertpulse{0%,100%{opacity:1}50%{opacity:.55}}
    </style>
    <script>
    var audioCtx=null, lastKey=null, es=null, pollTimer=null;

    function ensureAudio(){
      try{
        if(!audioCtx){audioCtx=new (window.AudioContext||window.webkitAudioContext)();}
        if(audioCtx.state==='suspended'){audioCtx.resume();}
      }catch(e){audioCtx=null;}
      return audioCtx;
    }
    ['click','keydown','touchstart'].forEach(function(ev){
      document.addEventListener(ev,ensureAudio);
    });
    function beep(){
      var ctx=ensureAudio();
      if(!ctx){return;}
      var t0=ctx.currentTime;
      [0,0.30].forEach(function(offset){
        var osc=ctx.createOscillator();
        var gain=ctx.createGain();
        osc.type='square';
        osc.frequency.value=880;
        gain.gain.setValueAtTime(0.0001,t0+offset);
        gain.gain.exponentialRampToValueAtTime(0.35,t0+offset+0.02);
        gain.gain.exponentialRampToValueAtTime(0.0001,t0+offset+0.24);
        osc.connect(gain);
        gain.connect(ctx.destination);
        osc.start(t0+offset);
        osc.stop(t0+offset+0.26);
      });
    }

    function fmt(n){
      if(n===null||n===undefined||n===''){return '₹0';}
      var v=Number(n);
      return isNaN(v)?('₹'+n):('₹'+v.toLocaleString('en-IN'));
    }
    function td(text,cls){
      var e=document.createElement('td');
      if(cls){e.className=cls;}
      e.textContent=(text===null||text===undefined)?'':String(text);
      return e;
    }
    function txRow(t){
      var tr=document.createElement('tr');
      tr.className='ok new';
      tr.appendChild(td(t.meal_date,'date'));
      tr.appendChild(td(String(t.created_at||'').slice(11,19),'date'));
      var s=document.createElement('td');
      s.appendChild(document.createTextNode((t.name||'')+' '));
      var code=document.createElement('span');
      code.className='muted';
      code.textContent=t.student_code||'';
      s.appendChild(code);
      tr.appendChild(s);
      tr.appendChild(td(t.meal_type));
      tr.appendChild(td(fmt(t.amount),'amount'));
      tr.appendChild(td(fmt(t.balance_after)));
      var st=document.createElement('td');
      var p=document.createElement('span');
      p.className='pill pill-ok';
      p.textContent='Success';
      st.appendChild(p);
      tr.appendChild(st);
      return tr;
    }
    function addTx(t){
      if(!t){return;}
      var body=document.getElementById('txbody');
      if(!body){return;}
      var empty=document.getElementById('txempty');
      if(empty){empty.parentNode.removeChild(empty);}
      body.insertBefore(txRow(t),body.firstChild);
      while(body.rows.length>200){body.deleteRow(body.rows.length-1);}
      var c=document.getElementById('txcount');
      if(c){c.textContent='Showing the latest '+body.rows.length+' transactions.';}
    }

    function setMode(mode){
      document.body.classList.remove('ok-mode','alert-mode');
      if(mode==='ok'){document.body.classList.add('ok-mode');}
      if(mode==='alert'){document.body.classList.add('alert-mode');}
    }
    function setBanner(kind,text){
      var b=document.getElementById('status-box');
      if(!b){return;}
      b.className='status '+(kind||'');
      b.textContent=text||'';
    }
    function renderScan(p){
      var el=document.getElementById('scan');
      if(!el){return;}
      var x=p.result||{};
      var ok=(x.status==='success');
      el.className='';
      el.innerHTML='';
      var badge=document.createElement('span');
      badge.className='pill '+(ok?'pill-ok':(x.status==='outside_meal_time'?'pill-neutral':'pill-warn'));
      badge.textContent=ok?'Approved':(x.status==='duplicate'?'Duplicate':(x.status==='unknown_student'?'Not registered':(x.status==='outside_meal_time'?'Closed':'Scan')));
      el.appendChild(badge);
      var head=document.createElement('p');
      head.style.cssText='margin:12px 0 0;font-size:18px;font-weight:600';
      head.textContent=x.student||(x.status==='unknown_student'?'Unregistered barcode':'');
      if(head.textContent){el.appendChild(head);}
      var lines=[
        x.meal?'Meal: '+x.meal:'',
        x.amount!==undefined?'Deduction: '+fmt(x.amount):'',
        x.balance!==undefined?'Balance after: '+fmt(x.balance):'',
        x.message||''
      ].filter(Boolean);
      lines.forEach(function(t){
        var p2=document.createElement('p');
        p2.style.margin='4px 0';
        p2.textContent=t;
        el.appendChild(p2);
      });
      var foot=document.createElement('p');
      foot.className='muted';
      foot.style.margin='10px 0 0';
      foot.textContent='Barcode: '+(p.barcode||p.data||'')+(p.detected_at?' · '+p.detected_at:'');
      el.appendChild(foot);
    }

    function handleScan(p,silent){
      if(!p||!p.result){return;}
      renderScan(p);
      var x=p.result;
      if(p.alert){
        if(!silent){beep();}
        setMode('alert');
        setBanner('alert',p.alert.message);
      }else if(x.status==='success'){
        setMode('ok');
        setBanner('ok','Approved · '+(x.student||'')+' · '+(x.meal||'')+' · '+fmt(x.amount)+' · balance '+fmt(x.balance));
      }else if(x.status==='duplicate'){
        setMode('alert');
        setBanner('alert',(x.student?x.student+' · ':'')+'Duplicate scan - already claimed today');
      }else{
        setMode('');
        setBanner('neutral',x.message||'Scan received');
      }
      addTx(p.tx);
    }

    function startPolling(){
      if(pollTimer){return;}
      pollTimer=setInterval(function(){
        fetch('/scan').then(function(r){return r.json();}).then(function(d){
          if(!d||!d.detected||!d.result){return;}
          var key=(d.detected_at||'')+'|'+(d.data||'');
          if(key===lastKey){return;}
          lastKey=key;
          handleScan({result:d.result,alert:d.alert,barcode:d.data,detected_at:d.detected_at});
        }).catch(function(){});
      },1000);
    }
    function stopPolling(){
      if(pollTimer){clearInterval(pollTimer);pollTimer=null;}
    }
    function connect(){
      if(!window.EventSource){startPolling();return;}
      es=new EventSource('/events');
      es.onopen=function(){stopPolling();};
      es.onmessage=function(e){
        try{
          var d=JSON.parse(e.data);
          if(d&&d.type==='scan'){
            lastKey=(d.detected_at||'')+'|'+(d.barcode||'');
            handleScan(d);
          }
        }catch(err){}
      };
      es.onerror=function(){startPolling();};
    }

    // Show the last scan (if any) without beeping on page load.
    fetch('/scan').then(function(r){return r.json();}).then(function(d){
      if(d&&d.detected&&d.result){
        lastKey=(d.detected_at||'')+'|'+(d.data||'');
        handleScan({result:d.result,alert:d.alert,barcode:d.data,detected_at:d.detected_at},true);
      }
    }).catch(function(){});
    connect();
    </script>
    """
    return page("Scanner & transactions", render_template_string(body, active=active, prices=MEAL_PRICES, rows=rows, money=money))

@APP.route("/video")
def video():
    return Response(generate_frames(), mimetype="multipart/x-mixed-replace; boundary=frame")

@APP.route("/scan")
def scan():
    """Latest completed scan. Used as a fallback when SSE is unavailable."""
    with barcode_lock:
        state = dict(last_scan)
    if state["result"] is None or time.time() - state["at"] > 30:
        return jsonify({"detected": False})
    return jsonify({
        "detected": True,
        "data": state["barcode"],
        "result": state["result"],
        "alert": state["alert"],
        "detected_at": state["detected_at"],
    })

@APP.route("/events")
def events():
    """Server-Sent Events stream: pushes every scan and new transaction."""
    sub = queue.Queue(maxsize=64)
    with subscribers_lock:
        subscribers.append(sub)

    def stream():
        try:
            yield "retry: 2000\n\n"
            while True:
                try:
                    payload = sub.get(timeout=15)
                    yield "data: " + payload + "\n\n"
                except queue.Empty:
                    yield ": ping\n\n"
        finally:
            with subscribers_lock:
                if sub in subscribers:
                    subscribers.remove(sub)

    return Response(stream(), mimetype="text/event-stream",
                    headers={"Cache-Control": "no-cache",
                             "X-Accel-Buffering": "no",
                             "Connection": "keep-alive"})

@APP.route("/api/student/<barcode>")
def api_student(barcode):
    with db() as con:
        s = con.execute("SELECT student_code,name,department,year,barcode,balance,package_start,package_end FROM students WHERE barcode=?",
                        (barcode,)).fetchone()
    return jsonify(dict(s) if s else {"error": "Student not found"}), (200 if s else 404)

@APP.route("/health")
def health():
    return jsonify({"status": "ok", "camera": camera_kind or "not_started",
                    "database": DB_PATH, "active_meal": get_active_meal()})

if __name__ == "__main__":
    init_db()
    try:
        start_camera()
        print(f"Smart Mess running at http://0.0.0.0:{PORT}")
        APP.run(host="0.0.0.0", port=PORT, threaded=True, use_reloader=False)
    finally:
        if camera is not None:
            if camera_kind == "picamera2":
                camera.stop()
            else:
                camera.release()
