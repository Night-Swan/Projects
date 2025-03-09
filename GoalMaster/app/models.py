import sqlalchemy as sa
import sqlalchemy.orm as so
from app import db
from werkzeug.security import generate_password_hash, check_password_hash
from datetime import datetime
from enum import Enum

class TaskStatus(Enum):
    TODO = "todo"
    IN_PROGRESS = "in_progress"
    DONE = "done"

class User(db.Model):
    __tablename__ = 'users'

    id: so.Mapped[int] = so.mapped_column(primary_key=True)
    username: so.Mapped[str] = so.mapped_column(sa.String(64), unique=True, index=True)
    email: so.Mapped[str] = so.mapped_column(unique=True, index=True)
    hashed_password: so.Mapped[str] = so.mapped_column()
    task: so.WriteOnlyMapped['Task'] = so.relationship(back_populates='user')

    def __repr__(self):
        return f'<User {self.username}>'
    
    def create_password(self, password):
        self.hashed_password = generate_password_hash(password)
    
    def check_password(self, password):
        return check_password_hash(self.hashed_password, password)

class Task(db.Model):
    __tablename__ = 'tasks'

    id: so.Mapped[int] = so.mapped_column(primary_key=True)
    user_id: so.Mapped[int] = so.mapped_column(sa.ForeignKey('users.id'), index=True)
    user: so.Mapped['User'] = so.relationship(back_populates='task')
    title: so.Mapped[str] = so.mapped_column(sa.String(64))
    description: so.Mapped[str] = so.mapped_column(sa.String(200))
    due_date: so.Mapped[datetime] = so.mapped_column(sa.DateTime)
    status: so.Mapped[TaskStatus] = so.mapped_column(sa.Enum(TaskStatus))
    created_at: so.Mapped[datetime] = so.mapped_column(sa.DateTime)
    updated_at: so.Mapped[datetime] = so.mapped_column(sa.DateTime)