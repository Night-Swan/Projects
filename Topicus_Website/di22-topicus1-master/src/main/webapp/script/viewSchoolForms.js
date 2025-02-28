import { FormStatus } from "./formUtils.js";
import {getSessionSchoolID} from "./storageManagement.js";

const selectedSchool = { "school_id": getSessionSchoolID() };

/**
 *  RegistrationFormMetadata class
 */
class RegistrationFormMetadata {
    constructor(registration_form_id, school_id, title, description, year, form_style, education_type, isdeleted, isactive) {
        this.registration_form_id = registration_form_id;
        this.school_id = school_id;
        this.title = title;
        this.description = description;
        this.year = year;
        this.form_style = form_style;
        this.education_type = education_type;
        this.isdeleted = isdeleted;
        this.isactive = isactive;
    }
}

//TODO: ADD LOAD HERE
window.addEventListener("load", queryFormsForSchool(selectedSchool["school_id"]));

/**
 * Query the api for the forms of the selected school
 * @param {*} school_id 
 */
function queryFormsForSchool(school_id) {
    let url = "/Topicus/api/schools/" + school_id + "/forms/metadata";
    fetch(url).then(response => response.json()).then(forms => {
        if (forms !== null && forms !== undefined) {
            let parsedForms = parseRegistrationFormsMetadata(forms);
            if (parsedForms.length == 0) {
                document.getElementById("content").innerHTML = "<h1> No forms found for this school </h1>";
                return;
            }
            populateForms(parsedForms);
        }

    });
}

/**
 * Parse the json objects to RegistrationFormMetadata objects
 * @param {*} forms
 * @returns {RegistrationFormMetadata[]}
 */
function parseRegistrationFormsMetadata(forms) {
    let parsedForms = [];

    forms.forEach(form => {
        let parsedForm = parseRegistrationForm(form);
        parsedForms.push(parsedForm);
    });

    return parsedForms;
}

/**
 * Parse the json object to a RegistrationFormMetadata object
 * @param {*} form
 * @returns {RegistrationFormMetadata}
 */
function parseRegistrationForm(form) {
    let parsedForm = new RegistrationFormMetadata(form["registration_form_id"], form["school_id"], form["title"], form["description"], form["year"], form["form_style"], form["education_type"], form["isdeleted"], form["isactive"]);
    return parsedForm;
}

/**
 * Populate the forms in the html
 * @param {*} forms
 */
function populateForms(forms) {
    let html_content = document.getElementsByClassName("content")[0];
    html_content.innerHTML = "";
    let forms_div = document.createElement("div");
    forms_div.setAttribute("id", "forms");

    forms.forEach(form => {
        let form_div = createFormDiv(form);
        forms_div.appendChild(form_div);
    });

    html_content.appendChild(forms_div);
}

/**
 * Create a div for a form
 * @param {*} form
 * @returns {HTMLDivElement}
 */
function createFormDiv(form) {
    let form_div = document.createElement("div");
    form_div.setAttribute("class", "form");
    form_div.setAttribute("id", form["registration_form_id"]);

    let form_title = document.createElement("div");
    form_title.innerHTML = form["title"];
    form_title.setAttribute("class", "form_title");
    form_div.appendChild(form_title);

    let form_description = document.createElement("div");
    form_description.innerHTML = form["description"];
    form_description.setAttribute("class", "form_description");
    form_div.appendChild(form_description);

    let form_year = document.createElement("div");
    form_year.innerHTML = form["year"];
    form_year.setAttribute("class", "form_year");
    form_div.appendChild(form_year);

    form_div.appendChild(createFormFooterButtons());

    return form_div;
}

/**
 * Create the footer buttons for a form
 * @returns {HTMLDivElement}
 */
function createFormFooterButtons() {
    let form_footer = document.createElement("div");
    form_footer.setAttribute("id", "footer_buttons");

    form_footer.appendChild(createFormViewButton());
    form_footer.appendChild(createFormEditButton());

    return form_footer;
}

/**
 * Create a view button for a form
 * @returns {HTMLButtonElement}
 */
function createFormViewButton() {
    let form_button = document.createElement("button");
    form_button.setAttribute("class", "button");
    form_button.innerHTML = "View";
    form_button.addEventListener("click", async function () {
        await queryRegistrationForm(this.parentElement.parentElement.id);
        window.location.href = "viewFormSchoolAdmin.html?school_id=" + selectedSchool["school_id"] + "&form_id=" + this.parentElement.parentElement.id;
    });
    return form_button;
}

/**
 * Create an edit button for a form
 * @returns {HTMLButtonElement}
 */
function createFormEditButton() {
    let form_button = document.createElement("button");
    form_button.setAttribute("class", "button");
    form_button.innerHTML = "Edit";
    form_button.addEventListener("click", async function () {
        await queryRegistrationForm(this.parentElement.parentElement.id);
        window.location.href = "/Topicus/registrationadmin.html";
    });
    return form_button;
}

async function queryRegistrationForm(form_id) {
    let url = "/Topicus/api/schools/" + selectedSchool["school_id"] + "/forms/" + form_id;
    console.log(url);
    await fetch(url).then(response => response.json()).then(form => {
        if (form !== null && form !== undefined) {
            console.log(form);
            console.log("here");
            sessionStorage.setItem("registrationFormDB", JSON.stringify(form));
            sessionStorage.setItem("formStatus", FormStatus.Edit.returnName());
        }
    });
}