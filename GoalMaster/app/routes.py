from app import app
from flask import render_template, jsonify, url_for, redirect
from flask_login import current_user, login_user 

@app.route("/")
@app.route("/index")
def index():
    return render_template("index.html", title="Index")

@app.route("/api/name")
def name():
    name = "Netherlands"
    return jsonify({"Name": name})

@app.route("/register", methods=['POST'])
def register():
    if current_user.is_authenticated:
        return redirect(url_for('index'))
            