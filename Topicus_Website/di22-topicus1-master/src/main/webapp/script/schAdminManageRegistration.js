// NECESSARY VARIABLES ---------------------------------------------------------------------------------------------
import {
    buildRegistrationURI,
    formBuilder,
    invalidSearch,
    parseDataFields,
    parseRegistration,
    parseSections,
    sectionBuilder,
    viewFields,
    Registration
} from "./manageRegistration.js";
import {generateDropDownForChangingStatus} from "./administratorUtils.js";
import {queryStyles, fieldValidator, sortList, formFieldGenerator, clearDiv} from "./formUtils.js";
import {getSessionUserID} from "./storageManagement.js";

const selectedRegistration = JSON.parse(sessionStorage.getItem("selectedRegistration"));
const admin_id = getSessionUserID();

let savedRegistration = null;
let savedDataFields = [];
let savedFormSections = [];
let chosenStatus = "UNCHANGED";

// CLASS ---------------------------------------------------------------------------------------------------------------
/**
 * Class for the status update request to be sent to the back-end.
 */
class RegistrationStatusUpdate {
    constructor(registration_id, status) {
        this.registration_id = registration_id;
        this.status = status;
    }
}

/**
 * Class for sending the modification to the back-end to be created.
 */
class ModificationCreationRequest {
    constructor(sa_id, reg_id, description, visibility) {
        this.sa_id = sa_id;
        this.reg_id = reg_id;
        this.description = description;
        this.visibility = visibility;
    }
}

/**
 * Class for the incoming Modifications to be viewed clearly.
 */
export class ModificationListView {
    constructor(date, sa_id, surname, reg_id, description, visible) {
        this.date = date;
        this.sa_id = sa_id;
        this.surname = surname;
        this.reg_id = reg_id;
        this.description = description;
        this.visible = visible;
    }
}

/**
 * Section class (duplicated due to issues). Move all classes to one JS file.
 */
class Section {
    constructor(section_id, registration_form_id, position, title) {
        this.section_id = section_id;
        this.registration_form_id = registration_form_id;
        this.position = position;
        this.title = title;
    }
}

// ON START-UP --------------------------------------------------------------------------------------------------------

/**
 * This method is executed on the HTML file for the viewing of the form for an administrator.
 */
window.addEventListener("load", async function() {
    if (window.location.pathname.includes("/Topicus/viewRegistrationSchAdmin.html")) {
        await queryRegistrationDetails();
    }
});

/**
 * This method is used to launch the query that returns the document view and the corresponding orientation of the page.
 * @returns {Promise<void>}
 */
async function queryRegistrationDetails() {
    clearDiv(document.getElementById("content_space"));
    let URI = buildRegistrationURI(selectedRegistration);
    await performFetchRegistration(savedRegistration, savedDataFields, savedFormSections, URI);
}

// FETCH FUNCTIONS -----------------------------------------------------------------------------------------------------

/**
 * The method that gets the details of the registration from the back-end.
 * @param registration
 * @param fields_list
 * @param sections_list
 * @param URI
 * @returns {Promise<void>}
 */
async function performFetchRegistration(registration, fields_list, sections_list, URI) {
    try {
        const response = await fetch(URI);
        if (!response.ok) {
            throw new Error("Registration Details Unavailable At This Time!");
        }
        const registrationContainer = await response.json();
        if (registrationContainer !== null && registrationContainer !== undefined) {
            /** @type {RegistrationContainer} */
            const container = registrationContainer;
            if (container.reg != null && container.df_pos != null && container.sections != null) {
                registration = parseRegistration(container.reg);
                chosenStatus = registration.status;
                fields_list = parseDataFields(container.df_pos);
                sections_list = parseSections(container.sections);
                let body = createFormBody(registration, fields_list, sections_list);
                const dropdown = generateDropDownForChangingStatus();
                const box = generateModificationLogBox();
                const inputSpace = document.getElementById("content_space");
                inputSpace.innerHTML = formBuilder(body);
                inputSpace.appendChild(generateDropdownDescription());
                inputSpace.appendChild(dropdown);
                inputSpace.appendChild(box);
                inputSpace.appendChild(generateCheckBox());
                inputSpace.innerHTML += '<button id="saveRegistrationStatus">Save</button> <button id="cancelRegistrationStatus">Cancel</button>';
                generateButtonsForSubmission();
                applyDropDownFunctionality();
                let URI2 = "./api/registrations/" + selectedRegistration.registration_id + "/modifications";
                await performModificationsFetch(URI2, inputSpace);
                await queryStyles(registration.registrationID, registration.registrationFormID, "content_space", "content-input", "section-name");
            } else {
                invalidSearch();
            }
        } else {
            invalidSearch();
        }
    } catch (Error) {
        console.log("An error occurred during the retrieval of information.");
    }
}

/**
 * This method is used to apply the functionality to change the status of the registration.
 */
function applyDropDownFunctionality() {
    const button = document.getElementById("dropdown_button");
    button.addEventListener("change", () => {
        chosenStatus = button.value;
    });
}

/**
 * This method creates the check-box that will be used to decide whether parents can see the modification or not.
 * @returns {HTMLDivElement}
 */
function generateCheckBox() {
    const checkBoxContainer = document.createElement("div");
    checkBoxContainer.id = "checkBoxContainer";
    checkBoxContainer.classList.add("checkBox");
    const checkBox = document.createElement("input");
    checkBox.type = "checkbox";
    checkBox.id = "include_parents";
    const label = document.createElement("label");
    label.htmlFor = "include_parents";
    label.textContent = "Show Modification to Parents?"
    checkBoxContainer.appendChild(label);
    checkBoxContainer.appendChild(checkBox);
    return checkBoxContainer;
}

/**
 * This method will enable the school administrator to see the historical changes.
 * @param URI
 * @param content_div
 * @returns {Promise<void>}
 */
async function performModificationsFetch(URI, content_div) {
    try {
        const response = await fetch(URI);
        if (!response.ok) {
            throw new Error("Registration Details Unavailable At This Time");
        }
        const mod_list = await response.json();
        if (mod_list !== null && mod_list !== undefined) {
            const views = parseModificationViews(mod_list);
            let body = "";
            body += generateModificationViews(views);
            const elem = document.createElement("div");
            elem.setAttribute("id", "modification_list");
            elem.innerHTML = body;
            content_div.appendChild(elem);
        }
    } catch (Error) {
        alert("Historical modifications could not be loaded.");
    }
}

/**
 * This functionality is to save the changes to the status of the registration, and also the modification details.
 * @param status
 * @param modification_text
 * @param visible
 * @returns {Promise<void>}
 */
async function saveChanges(status, modification_text, visibility) {
    await saveStatus(status);
    await saveModification(modification_text, visibility);
}

/**
 * This functionality is to save the status.
 * @param status
 * @returns {Promise<void>}
 */
async function saveStatus(status) {
    let URI = "./api/registrations/" + selectedRegistration.registration_id;
    console.log(selectedRegistration.registration_id);
    try {
        const response = await fetch(URI, {
            headers: {
                "Content-Type": "application/json"
            },
            method: "PUT",
            body: JSON.stringify((new RegistrationStatusUpdate(selectedRegistration.registration_id, chosenStatus)))
        });
        if (!response.ok) {
            throw new Error("Error making connection with server.");
        }
        const reg = await response.json();
        if (reg !== null && reg !== undefined) {
            /** @type {Registration} */
            const registration = parseRegistration(reg);
            console.log(JSON.stringify(registration));
        }
    } catch (Error) {
        invalidSearch();
    }
}

/**
 * This functionality is to save the modification.
 * @param modification_text
 * @returns {Promise<void>}
 */
async function saveModification(modification_text, visibility) {
    let URI = "./api/registrations/" + selectedRegistration.registration_id + "/modifications";
    try {
        const response = await fetch(URI, {
            headers: {
                "Content-Type": "application/json"
            },
            method: "POST",
            body: JSON.stringify(new ModificationCreationRequest(admin_id, selectedRegistration.registration_id, modification_text, visibility))
        });
        if (!response.ok) {
            throw new Error("Could not make connection with DB");
        }
        const modification = await response.json();
        if (modification !== null && modification !== undefined) {
            alert("Your request was successful!");
            window.location.href = "/Topicus/schooladmindashboard.html";
        }
    } catch (Error) {
        alert("Something went wrong, please try again later!");
    }
}

// PARSING ---------------------------------------------------------------------------------------------------
/**
 * This method is for parsing the modifications after they are retrieved from the server.
 * @param mv_list
 * @returns {*[]}
 */
export function parseModificationViews(mv_list) {
    console.log(JSON.stringify(mv_list));
    const modViews = [];
    if (mv_list.length === 0) {
        invalidSearch();
    } else {
        let propertyNames = Object.keys(mv_list[0]);
        for (const mv of mv_list) {
            if (fieldValidator(propertyNames, mv)) {
                const view = new ModificationListView(
                    mv[propertyNames.at(0)],
                    mv[propertyNames.at(1)],
                    mv[propertyNames.at(2)],
                    mv[propertyNames.at(3)],
                    mv[propertyNames.at(4)],
                    mv[propertyNames.at(5)]);
                modViews.push(view);
                console.log("View validated");
            }
        }
    }
    return modViews;
}

/**
 * Method used to create the body of the form.
 * @param reg is Registration.
 * @param dfs is List of Data Fields.
 * @param sects is Sections.
 * @returns {string}
 */
function createFormBody(reg, dfs, sects) {
    let body = "<p><h3>Current Status: " + reg["status"] + "</h3></p>";
    const sortedSections = sortList(sects, "position");
    const sortedDataFields = sortList(dfs, "position");
    for (const section of sortedSections) {
        body += sectionBuilder(section["title"]);
        for (const dataf of sortedDataFields) {
            if (dataf["sectionID"] === section["sectionID"]) {
                body += formFieldGenerator(dataf["title"], dataf["content"], dataf["mandatory"], dataf["dataType"], true).outerHTML;
                console.log("Added Form Field to HTML");
            }
        }
    }
    return body;
}

/**
 * This method creates the description for the dropdown.
 * @returns {HTMLElement}
 */
function generateDropdownDescription() {
    let result = '<p><h3>The drop-down below is to select the status of the registration.</h3></p>';
    const elem = document.createElement("div");
    elem.setAttribute("id", "description");
    elem.innerHTML = result;
    return elem;
}

/**
 * The modification box is created.
 * @returns {HTMLFormElement}
 */
function generateModificationLogBox() {
    let result =
        '<textarea class="content-input" id="textSpace" autofocus rows="10" cols="60" placeholder="Enter comment here"></textarea>';
    const modificationForm = document.createElement("form");
    modificationForm.setAttribute("id", "modification_space");
    modificationForm.innerHTML = result;
    return modificationForm;
}

/**
 * Method to generate the functionalities for the buttons.
 */
function generateButtonsForSubmission() {
    const saveButton = document.getElementById("saveRegistrationStatus");
    const cancelButton = document.getElementById("cancelRegistrationStatus");
    saveButton.addEventListener("click", async function() {
        if (performChecks()) {
            const box = document.getElementById("include_parents");
            if (box.checked) {
                await saveChanges(chosenStatus, document.getElementById("textSpace").value, "true");
            } else {
                await saveChanges(chosenStatus, document.getElementById("textSpace").value, "false");
            }
        }
    });
    cancelButton.addEventListener("click", function() {
        alert("Your changes will not be saved.");
        returnToDashboard();
    });
}

/**
 * This function is used to enclose the header values for the row.
 * @returns {string}
 * @param view
 * @param idElement
 */
function encloseHeader(view, className) {
    const propertyNames = Object.keys(view);
    let result ='<div class="form-box">' +
        '<div class="context-box">';

    for (const key of propertyNames) {
        result += "<div id=idElement>";
        result += "<label class='" + className + "'>" + key + ": " + "</label>";
        result += "<span class='view_key'>" + view[key] + "</span>";
        result += "</div>";
    }
    result += "</div>" + "</div>";
    return result;
}

/**
 * Method for generating the view of the ModificationViews.
 * @param view_list
 */
function generateModificationViews(view_list) {
    let result = "";
    for (const view of view_list) {
        result += encloseHeader(view, "mod_title") + "<br>";
    }
    return result;
}

/**
 * Checks if any changes have actually been made.
 * @returns {boolean}
 */
function performChecks() {
    let textInput = document.getElementById("textSpace").value;
    return (textInput !== null && textInput !== "" && chosenStatus !== "UNCHANGED");
}

/**
 * Method to return to the dashboard.
 */
function returnToDashboard() {
    window.location.href = "/Topicus/schooladmindashboard.html";
}