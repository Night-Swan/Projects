from flask_wtf import FlaskForm
from wtforms import StringField, PasswordField, BooleanField, SubmitField
from wtforms.validators import DataRequired, ValidationError, Email, EqualTo
import sqlalchemy as sa
from app import db


class RegistrationForm(FlaskForm):
    username = StringField('Username', validators=[DataRequired()])
