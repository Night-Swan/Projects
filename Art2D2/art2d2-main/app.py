import json
import requests
from flask import Flask, render_template, jsonify, request, session
import re

from OllamaCallPythonCode.ollamaCall import answerQuestionAboutPainting

app = Flask(__name__)
app.secret_key = 'your_secret_key'  # Required for session management

# Sample artwork list
artworkList = {
    'Composition with Red, Blue and Yellow': 'Painted by Piet Mondrian, a Dutch artist of the Neo-Plasticism movement, in 1930. This piece demonstrates the artist\'s commitment to opposites, symmetry, and pre-planes of color. The painting is emblematic of Mondrian\'s avant-garde abstract art style.',
    'Black Square': 'Painted by Kazimir Malevich, a Ukrainian avant-garde artist, there are four versions of this work, made in 1915, 1923, 1929, and somewhere between 1935-1945. His work was heavily influenced by Impressionism. Black Square is regarded as a foundational work in the development of modern and abstract art. The painting itself belongs to the Suprematism movement according to its creator, emphasizing shape and color.',
    'Red Square': 'Painted by Kazimir Malevich, a Ukrainian avant-garde artist. His work was heavily influenced by Impressionism. Red Square is regarded as a foundational work in the development of modern and abstract art. The painting itself belongs to the Suprematism movement according to its creator, emphasizing shape and color.'
}

# Home Page
@app.route('/')
def home():
    return render_template('home.html')

# QR Scanner Page
@app.route('/scan')
def scan():
    return render_template('scan.html')

# Database Page
@app.route('/database')
def database():
    paintings = [
        {"name": "Composition with Red, Blue and Yellow", "artist": "Piet Mondrian", "year": "1930"},
        {"name": "Black Square", "artist": "Kazimir Malevich", "year": "1915-1923"},
        {"name": "Red Square", "artist": "Kazimir Malevich", "year": "1915"}
    ]
    return render_template('database.html', paintings=paintings)

# Chat Page
@app.route('/chat/<painting_name>')
def chat(painting_name):
    # Track visited paintings for the user
    if 'visited_paintings' not in session:
        session['visited_paintings'] = []
    if painting_name not in session['visited_paintings']:
        session['visited_paintings'].append(painting_name)
    return render_template('chat.html', painting=painting_name)

# Generate Quiz Based on Visited Paintings
@app.route('/generate-quiz', methods=['POST'])
def generate_quiz():
    if 'visited_paintings' not in session or not session['visited_paintings']:
        return jsonify({'error': 'No paintings visited yet.'}), 400

    # Get descriptions of visited paintings
    visited_paintings = session['visited_paintings']
    painting_descriptions = [artworkList.get(painting, '') for painting in visited_paintings]

    # Create a prompt for the LLM to generate a quiz
    prompt = (
        "Using the following descriptions of paintings:\n" +
        "\n".join([f"{painting}: {description}" for painting, description in zip(visited_paintings, painting_descriptions)]) +
        "\nCreate a multiple-choice quiz with 3 questions. Format each question as: {question: ..., choices: [...], answer: ...}"
    )

    # Call Ollama to generate the quiz
    quiz_data = call_ollama(prompt)
    print("Quiz Data from Ollama:", quiz_data)  # Log the raw quiz data

    if quiz_data:
        parsed_quiz = parse_quiz_response(quiz_data)
        print("Parsed Quiz:", parsed_quiz)  # Log the parsed quiz data
        return jsonify({'quiz': parsed_quiz})
    else:
        return jsonify({'error': 'Failed to generate quiz.'}), 500
@app.route('/ask-question', methods=['POST'])
def ask_question():
    data = request.get_json()
    painting = data.get('painting')
    question = data.get('question')

    if not painting or not question:
        return jsonify({"error": "Invalid request, painting or question missing."}), 400

    # Generate bot response using your `answerQuestionAboutPainting` function
    bot_response = answerQuestionAboutPainting(painting, question)
    return jsonify({"answer": bot_response})

# Helper Function to Call Ollama
def call_ollama(prompt):
    url = 'http://127.0.0.1:11434/api/generate'
    ollamaObject = {'model': 'llama3.2', 'prompt': prompt, 'stream': False}

    try:
        response = requests.post(url, json=ollamaObject)
        if response.status_code == 200:
            return response.json().get('response')
        else:
            print('Error:', response.status_code)
            return None
    except Exception as e:
        print(e)
        return None

import re

def parse_quiz_response(text):
    questions = []
    # Split the text into individual question blocks
    question_blocks = re.split(r'\n\n', text.strip())

    for block in question_blocks:
        # Remove trailing '}' if present
        block = block.rstrip('}').strip()

        # Extract the question
        question_match = re.search(r'question:\s*(.*?)\s*choices:', block, re.DOTALL)
        if not question_match:
            continue  # Skip if no question is found
        question = question_match.group(1).strip()

        # Remove trailing commas and spaces
        question = question.rstrip(',?')  # Remove trailing comma
        question = question.strip()  # Remove any extra spaces

        # Ensure the question ends with a single "?"
        if not question.endswith('?'):
            question += '?'

        # Extract the choices
        choices_match = re.search(r'choices:\s*\[(.*?)\]', block, re.DOTALL)
        if not choices_match:
            continue  # Skip if no choices are found
        choices = [choice.strip().strip('"') for choice in choices_match.group(1).split(',')]

        # Extract the answer
        answer_match = re.search(r'answer:\s*(.*)', block)
        if not answer_match:
            continue  # Skip if no answer is found
        answer = answer_match.group(1).strip().strip('"').rstrip('}')  # Remove trailing '}'

        # Add the structured question to the list
        questions.append({
            "question": question,
            "choices": choices,
            "answer": answer  # Directly include the answer text
        })

    return questions
if __name__ == '__main__':
    app.run(host='0.0.0.0', port=8080, debug=True)