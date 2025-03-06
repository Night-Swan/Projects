import os

current_directory = os.path.abspath((os.path.dirname(__name__)))

class Config:
    SECRET_KEY = os.environ.get('SECRET_KEY') or 'nice_secret_key'
    SQLALCHEMY_DATABASE_URI = 'sqlite:///' + os.path.join(current_directory, 'goalmaster.db')
    JWT_SECRET_KEY = 'new_nice_secret_key'

