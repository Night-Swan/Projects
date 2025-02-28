import { inputSanitizer, isEmpty, validEmail } from "../fe_security/inputsanitizer.js";
import { get, post, put } from "./requests.js";

const signupButton = document.getElementById('signup-button');
signupButton.addEventListener('click', onSubmit);

// Creates users of type 'TOPICUS_ADMIN' | 'SCHOOL_ADMIN' | 'GUARDIAN'
export async function createUser(type, username, email, password, person_id) {
    if (type !== 'TOPICUS_ADMIN' && type !== 'SCHOOL_ADMIN' && type !== 'GUARDIAN') {
        alert('Invalid account type request!');
        throw new Error(`User type '${type}' is invalid!`);
    }
    
    const hasGID = (person_id !== null && person_id !== undefined && person_id !== "");
    const URI = './api/users';
    const data = { type, username, email, password };
    const result = await post(URI, data);
    console.log(result);
    
    if (result !== undefined && result !== null) {
        if (hasGID) {
            //Get guardian object details
            const getGuardianURI = `./api/parents/${person_id}`;
            const guardian = await get(getGuardianURI);
            
            //Update guardian details with account_id
            const putGuardianURI = `./api/parents/${person_id}`;
            guardian["account_id"] = result["account_id"];
            const updatedGuardian = await put(putGuardianURI, guardian);
            console.log(updatedGuardian);

            if (updatedGuardian === undefined || updatedGuardian === null) {
                alert('Connecting your account with your Guardian Code failed!');
                throw new Error('Connecting account with Guardian Code failed!');
            }
        }
        return true;
    } else {
        alert('Sign up failed!');
        throw new Error('User creation failed!');
    }
}

// Executes user creation
async function onSubmit(event) {
    event.preventDefault();

    const username = document.getElementById('username').value.trim();
    const email = document.getElementById('email').value.trim();
    const password = document.getElementById('password').value.trim();
    const confirmPassword = document.getElementById('cpassword').value.trim();
    const guardian_id = document.getElementById('gid').value.trim();

    if (isEmpty(username) || isEmpty(email) || isEmpty(password)) {
        return alert('An input is empty!\n(Guardian Code is not taken into account, as it is an optional field)');
    } else if (password !== confirmPassword) {
        return alert('Passwords do not match');
    } else if (!inputSanitizer(username) || !inputSanitizer(email) || !validEmail(email) || !inputSanitizer(password) || !inputSanitizer(username) || (!isEmpty(guardian_id) && !inputSanitizer(guardian_id))) {
        return alert('Your username, email, password or guardian code is invalid. Please try again.');
    }

    const isCreated = await createUser('GUARDIAN', username, email, password, guardian_id);
    if (isCreated) {
        alert("Account created successfully!");
        window.location.href = "/Topicus/login.html";
    } else {
        alert("Something went wrong when creating new account!");
    }
}