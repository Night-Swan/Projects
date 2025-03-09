from app import app, db
from flask import render_template, jsonify, url_for, redirect, request
from .forms import RegistrationForm, LoginForm
from .models import User, Task
from flask_jwt_extended import create_access_token, jwt_required, get_jwt_identity
from flask_wtf.csrf import generate_csrf

@app.route("/")
@app.route("/index")
def index():
    return render_template("index.html", title="Index")

@app.route("/home")
@jwt_required()
def home():
    current_user_id = get_jwt_identity()
    return render_template("home.html")

@app.route("/api/name")
def name():
    name = "Netherlands"
    return jsonify({"Name": name})

@app.route("/get-csrf-token", methods=['GET'])
def get_csrf_token():
    return jsonify({"csrf_token": generate_csrf()})

@app.route("/register", methods=['GET', 'POST'])
def register():
    if request.method == 'GET':
        return render_template('register.html')
    registration_form = RegistrationForm()
    print("Form data:", request.form)         
    print("Form validated:", registration_form.validate())  
    print("Form errors:", registration_form.errors)  
    if registration_form.validate_on_submit():
        username = registration_form.username.data
        email = registration_form.email.data
        password = registration_form.password.data
        user = User(username=username, email=email)
        user.create_password(password)
        db.session.add(user)
        db.session.commit()
        return jsonify({"message": "User registered successfully"}), 201
    return jsonify({"error": "Form validation failed", "details": registration_form.errors}), 400


@app.route("/login", methods=['GET', 'POST'])
def login():
    login_form = LoginForm()
    if login_form.validate_on_submit():
        username = login_form.username.data
        password = login_form.password.data
        user = User.query.filter_by(username=username).first()
        
        if user and user.check_password(password):
            access_token = create_access_token(identity=user.id)
            return jsonify({'access_token': access_token}), 200
        return jsonify({"error": "Invalid credentials"}), 401
    return render_template('login.html', form=login_form)


@app.route('/protected', methods=['GET'])
@jwt_required()
def protected():
    current_user_id = get_jwt_identity()
    user = User.query.get(current_user_id)
    return jsonify({
        'username': user.username,
        'email': user.email
    }), 200

