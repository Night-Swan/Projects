from app import app
from flask import render_template, jsonify, url_for, redirect
from flask_login import current_user, login_user 
from .forms import RegistrationForm, LoginForm

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
    registration_form = RegistrationForm()
    if registration_form.validate_on_submit():
        new_user = registration_form()     