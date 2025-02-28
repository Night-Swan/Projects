//import { createUser } from "../script/signup.js";
import {get, post, put} from "./requests.js";
const school_id = sessionStorage.getItem("schoolID");
const form = document.getElementById("contact-form");
form.addEventListener("submit", onSubmit);
const button = document.getElementById("add-admin");
button.addEventListener("click",function() {
    window.location.href = '/Topicus/topicusadmindashboard.html';
})
async function onSubmit(event) {
    console.log(`School id ${school_id}`)
    event.preventDefault();
    //account data
    const username = document.getElementById("username").value;
    const email = document.getElementById("email").value;
    const password = document.getElementById("password").value;
    const confirmPassword = document.getElementById("confirmPassword").value;
    console.log(`THE DATA FOR USER: ${username}, ${email}, ${password}`);
    //school admin details
    const surname = document.getElementById("surname").value;
    const givenNames = (document.getElementById("givenNames").value).split(" ");
    const phone_number = document.getElementById("phone_number").value;
    const birth_date = document.getElementById("birth_date").value;
    console.log(`THE DATA FOR PERSONAL DETAILS: ${surname}, ${givenNames}, ${phone_number}, ${birth_date}`);
    if(password === confirmPassword) {
        const user = await createUser(username, email, password, undefined, 'SCHOOL_ADMIN');
        console.log("The newly created user id: " + user.account_id);
        await createSchoolAdmin(user.account_id, surname, phone_number, birth_date,givenNames, school_id, "");
    }
    else {
        alert("Password didn't match");
    }
    //window.location.href = '/Topicus/topicusadmindashboard.html';
}
async function createUser(username, email, password, guardian_id, type) {
    const URI = './api/users';
    const data = {type, username, email, password};
    try {
        const result = await post(URI, data);
        if(result.ok) {
            console.log("the post return for user: " + result.json);
            alert("User Added");
        }
        else {
            alert('User not added, error:' + result.status)
        }
        return result;
    } catch (error) {
        console.log("error when put request is made: " + error);
    }

}
async function createSchoolAdmin(adminID, surname, phoneNumber, birthDate, givenNames, schoolID, employeeID) {
    const URI = './api/users/school_admins';
    const data = {adminID, surname, phoneNumber, birthDate, givenNames ,schoolID ,employeeID};
    try {
        const result = await post(URI, data);
        if(result.ok) {
            console.log("the post return for school admin: ", result);
            alert("School Admin Added");
        }
        else {
            alert('School admin not added, error:' + result.status)
        }
        return result;
    } catch (error) {
        console.log("error when put request is made: " + error);
    }

}
