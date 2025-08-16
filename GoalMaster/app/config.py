import os
from dotenv import load_dotenv
load_dotenv()  

current_directory = os.path.abspath((os.path.dirname(__name__)))

class Config:
    SECRET_KEY = os.environ.get('SECRET_KEY')
    SQLALCHEMY_DATABASE_URI = 'sqlite:///' + os.path.join(current_directory, 'goalmaster.db')
    JWT_SECRET_KEY = os.environ.get('JWT_SECRET_KEY') 

    JWT_TOKEN_LOCATION = ['headers']  

