from app import app, db
from flask import render_template, jsonify, url_for, redirect, request
from .forms import RegistrationForm, LoginForm
from .models import User, Task, TaskStatus, TaskPriority
from flask_jwt_extended import create_access_token, jwt_required, get_jwt_identity
from flask_wtf.csrf import generate_csrf
from datetime import datetime


@app.route("/")
@jwt_required(optional=True)
def intro():
    current_user_id = get_jwt_identity()
    is_authenticated = current_user_id is not None
    return render_template("intro.html", is_authenticated=is_authenticated)

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
            access_token = create_access_token(identity=str(user.id))  
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


@app.route("/user/profile.html", methods=['GET'])
def serve_profile_page():
    return render_template('profile.html')

@app.route('/user/profile', methods=['GET'])
@jwt_required()
def user_profile():
    current_user_id = get_jwt_identity()
    print(f"Current user ID from token: {current_user_id}")  
    user = User.query.get(current_user_id)
    if user:
        return jsonify({
            "username": user.username,
            "email": user.email
        }), 200
    return jsonify({"error": "User not found"}), 404

@app.route('/tasks', methods=['POST'])
@jwt_required()
def create_task():
    current_user_id = get_jwt_identity()
    data = request.get_json()

    title = data.get('title')
    description = data.get('description')
    due_date_str = data.get('due_date')
    status_str = data.get('status', 'todo')
    status = TaskStatus(status_str.lower())
    priority_str = data.get('priority', 'high')
    priority = TaskPriority(priority_str.lower())

    if not title:
        return jsonify({"error": "Title is required"}), 400
    
    try:
        due_date = datetime.strptime(due_date_str, '%Y-%m-%d') if due_date_str else None
    except ValueError:
        return jsonify({"error": "Invalid due_date format. Use YYYY-MM-DD"}), 400
    
    task = Task(
        user_id = current_user_id,
        title = title,
        description = description,
        due_date = due_date,
        status = status,
        priority = priority,
        created_at = datetime.utcnow(),
        updated_at = datetime.utcnow()
    )
    db.session.add(task)
    db.session.commit()

    return jsonify({"message": "Task created successfully", "task_id": task.id}), 201


@app.route('/tasks', methods = ['GET'])
@jwt_required()
def get_tasks():
    current_user_id = get_jwt_identity()
    tasks = Task.query.filter_by(user_id = current_user_id).all()

    tasks_data = [{
        "id": task.id,
        "title": task.title,
        "description": task.description,
        "due_date": task.due_date.isoformat() if task.due_date else None,
        "status": task.status.value,
        "priority": task.priority.value,
        "created_at": task.created_at.isoformat(),
        "updated_at": task.updated_at.isoformat()
    } for task in tasks]

    return jsonify({"tasks": tasks_data}), 200


# Update a task
@app.route('/tasks/<int:task_id>', methods=['PUT'])
@jwt_required()
def update_task(task_id):
    current_user_id = get_jwt_identity()
    task = Task.query.filter_by(id=task_id, user_id=current_user_id).first()
    
    if not task:
        return jsonify({"error": "Task not found or not authorized"}), 404
    
    data = request.get_json()
    task.title = data.get('title', task.title)
    task.description = data.get('description', task.description)
    
    if 'due_date' in data:
        try:
            task.due_date = datetime.strptime(data['due_date'], '%Y-%m-%d') if data['due_date'] else None
        except ValueError:
            return jsonify({"error": "Invalid due_date format. Use YYYY-MM-DD"}), 400
    
    if 'status' in data:
        try:
            task.status = TaskStatus(data['status'])
        except ValueError:
            return jsonify({"error": "Invalid status. Use TODO, IN_PROGRESS, or DONE"}), 400
    
    if 'priority' in data:
        try:
            task.priority = TaskPriority(data['priority'])
        except ValueError:
            return jsonify({"error": "Invalid priority. Use TODO, IN_PROGRESS, or DONE"}), 400
        
    task.updated_at = datetime.utcnow()
    db.session.commit()
    
    return jsonify({"message": "Task updated successfully"}), 200

# Delete a task
@app.route('/tasks/<int:task_id>', methods=['DELETE'])
@jwt_required()
def delete_task(task_id):
    current_user_id = get_jwt_identity()
    task = Task.query.filter_by(id=task_id, user_id=current_user_id).first()
    
    if not task:
        return jsonify({"error": "Task not found or not authorized"}), 404
    
    db.session.delete(task)
    db.session.commit()
    
    return jsonify({"message": "Task deleted successfully"}), 200


@app.route('/tasks.html', methods=['GET'])
def serve_tasks_page():
    return render_template('tasks.html')
