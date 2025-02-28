import { updateNavOnLoad } from "./navigation.js";
import { get } from "./requests.js";
import { inputSanitizer, isEmpty } from "../fe_security/inputsanitizer.js";
import {
    getSessionUserID,
    getSessionUserType,
    setSession,
    setSessionGuardianID,
    setSessionSchoolID
} from "./storageManagement.js";

const loginBtn = document.getElementById('login-button');
loginBtn.addEventListener('click', onSubmit);

const enterButton = document.getElementById('proceed-button');
enterButton.addEventListener('click', onNoAccount);

/**
 * Logs in the user with username, email and password.
 * @param {Object} credentials is either { username, email, password } or { guardian_id }
 * @returns true on successful login
 */
async function login(credentials) {
    const URI = "./api/login";
    const options = {
        method: 'POST',
        headers: {
            'Content-type': 'application/json'
        },
        body: JSON.stringify(credentials)
    };
    //The request needs to await the promise as text, not as json.
    try {
        const response = await fetch(URI, options);
        console.log(response);
        if (!response.ok) {
            alert("Your credentials are incorrect!");
            throw new Error('Incorrect input');
        }
        await response.text();
        return true;
    } catch (error) {
        throw error;
    }
}

// ------ Login with an account
async function onSubmit(event) {
    event.preventDefault();

    const usernameInput = document.getElementById('username');
    const emailInput = document.getElementById('email');
    const passwordInput = document.getElementById('password');

    const username = usernameInput.value.trim();
    const email = emailInput.value.trim();
    const password = passwordInput.value.trim();

    if (isEmpty(username) || isEmpty(email) || isEmpty(password)) {
        return alert('All fields are required!');
    } else if (!inputSanitizer(username) || !inputSanitizer(email) || !inputSanitizer(password)) {
        return alert('Your username, email or password is invalid. Please enter again.');
    }

    const isLoggedIn = await login({ username, email, password });
    if (isLoggedIn) {
        setSession();
        updateNavOnLoad();
        await redirect();
    }
}

async function redirect() {
    const userType = getSessionUserType();
    if (userType === 'GUARDIAN') {
        const loginWithData = await loggedInWithData();
        if (loginWithData !== undefined && loginWithData !== null && loginWithData !== "") {
            setGuardianAndProceed(loginWithData.guardian_id);
        } else {
            loadFillDetails();
        }
    } else if (userType === 'SCHOOL_ADMIN') {
        const result = await setSchool();
        if (result) {
            window.location.href = "/Topicus/schooladmindashboard.html";
        }
    } else if (userType === 'TOPICUS_ADMIN') {
        window.location.href = "/Topicus/topicusadmindashboard.html";
    }
}

async function setSchool() {
    const URI = `./api/users/school_admins/${getSessionUserID()}/details`;
    const admin = await get(URI);
    if (admin !== null && admin !== undefined && admin.schoolID !== undefined) {
        setSessionSchoolID(admin.schoolID);
        console.log("School ID: " + admin.schoolID);
        return true;
    } else {
        alert("Could not reach server.");
        return false;
    }
}

/**
 * Checks if there is guardian data about this account.
 * @returns true if there is a guardian linked to that account
 */
async function loggedInWithData() {
    const URI = `./api/parents/accounts`;
    return await get(URI);
}

function loadFillDetails() {
    window.location.href = "/Topicus/fillDetails.html";
}

// ------ Login with a guardian_id - Guardians only
/**
 * Login with just a guardian_id and no account.
 * @param {Event} event 
 */
async function onNoAccount(event) {
    event.preventDefault();
    const guardian_id = document.getElementById('guardianCode').value;
    if (inputSanitizer(guardian_id) && !isEmpty(guardian_id)) {
        const URI = `./api/parents/${guardian_id}`;
        const logged = await get(URI);
        if (logged !== undefined && logged !== null) {
            setGuardianAndProceed(guardian_id);
        } else {
            throw new Error('Invalid Guardian Code!');
        }
    } else {
        throw new Error('Inappropriate input!');
    }
}

/**
 * Stores the guardian_id in sessionStorage and redirects to schools.
 * @param {string} guardian_id 
 */
function setGuardianAndProceed(guardian_id) {
    setSessionGuardianID(guardian_id);
    window.location.href = "/Topicus/schools.html";
}

