// IMPORTS -------------------------------------------------------------------------------------
import {PageStatus} from "./parentDashboard.js";
import {parseModificationViews} from "./schAdminManageRegistration.js"
import {
    queryStyles,
    generateMandatoryDTStrings,
    formFieldGenerator, validateDataField, fieldValidator, sortList
} from "./formUtils.js";
export { DataField, Registration, invalidSearch };

// OBJECTS -------------------------------------------------------------------------------------
const sReg = JSON.parse(sessionStorage.getItem("selectedRegistration"));
const pStatus = [];
pStatus[0] = sessionStorage.getItem("pageStatus");
const fileByteArrayContainer = [];

// CLASSES ----------------------------------------------------------------------------------

/**
 * Class for Data_Field as sent from server.
 */
class DataField {
    constructor(fieldID, registrationID, componentID, sectionID, title, content, position_number, mandatory, dataType) {
        this.fieldID = fieldID;
        this.registrationID = registrationID;
        this.componentID = componentID;
        this.sectionID = sectionID;
        this.title = title;
        this.content = content;
        this.position_number = position_number;
        this.mandatory = mandatory;
        this.dataType = dataType;
    }
}

/**
 * Class used to send data to the back-end.
 */
class BEDataField {
    constructor(fieldID, registrationID, content) {
        this.field_id = fieldID;
        this.registration_id = registrationID;
        this.content = content;
    }
}

/**
 * Class for Registration as sent from server.
 */
class Registration {
    constructor(registrationID, guardianID, childID, schoolID, registrationFormID, status) {
        this.registrationID = registrationID;
        this.guardianID = guardianID;
        this.childID = childID;
        this.schoolID = schoolID;
        this.registrationFormID = registrationFormID;
        this.status = status;
    }
}

/**
 * Class for Section as sent from the server.
 */
class Section {
    constructor(sectionID, registrationFormID, position, title) {
        this.sectionID = sectionID;
        this.registrationFormID = registrationFormID;
        this.position = position;
        this.title = title;
    }
}

/**
 * Class for understanding how response is sent from back-end.
 */
class RegistrationContainer {
    constructor(reg, df_pos, sections) {
        this.reg = reg;
        this.df_pos = df_pos;
        this.sections = sections;
    }
}

/**
 * Used to send an update for the Registration to the back-end.
 */
class RegistrationUpdate {
    constructor(registration_id, status) {
        this.registration_id = registration_id;
        this.status = status;
    }
}

// CONSTANTS --------------------------------------------------------------------------------------------------------------

// To update status after status query launched, update property of selectedRegistration.
let savedReg = null;
let savedFields = [DataField];
let savedSections = [Section];
export const invalidEditingStatus = ["ACCEPTED", "REJECTED", "SUBMITTED", "UNDER_REVIEW", "UNAVAILABLE_ERROR"];
const invalidDeletionStatus = ["ACCEPTED", "UNDER_REVIEW", "UNAVAILABLE_ERROR"];
const submissionButtonCriteria = ["AWAITING_SUBMISSION", "MODIFICATIONS_ALLOWED"];

// GENERAL METHODS (FOR BOTH EDITING/VIEWING) ------------------------------------------------------------------------------

/**
 * Event Listener for page being ready.
 */
window.addEventListener("load", async function() {
    if (window.location.pathname.includes("/Topicus/viewRegistrationParent.html")) {
        console.log("Executed query to load page");
        await queryDetails();
    }
});

/**
 * Method to show that it could not register the ID, and that an issue on the client-side has occurred.
 */
function invalidSearch() {
    alert("Something went wrong. Please refresh and try again.");
}

/**
 * This method is used to clear a div element on the page.
 * @param div
 */
function clearDiv(div) {
    div.innerHTML = "";
}

// PARSING METHODS --------------------------------------------------------------------------------------------------

/**
 * Method to parse the Registration that is provided in the server response entity.
 * @param registration of type Registration.
 */
export function parseRegistration(registration) {
    const registrationKeys = Object.keys(registration);
    if (fieldValidator(registrationKeys, registration)) {
        console.log("Registration Validated");
        return new Registration(registration[registrationKeys.at(0)],
            registration[registrationKeys.at(1)],
            registration[registrationKeys.at(2)],
            registration[registrationKeys.at(3)],
            registration[registrationKeys.at(4)],
            registration[registrationKeys.at(5)]);
    } else {
        return undefined;
    }
}

/**
 * Method to parse the DataFields that are sent as a map in the server response entity.
 * @param dataFieldList of type DataField[].
 */
export function parseDataFields(dataFieldList) {
    const dataFields = [];
    if (dataFieldList.length === 0) {
        invalidSearch();
    } else {
        let propertyNames = Object.keys(dataFieldList[0]);
        for (const df of dataFieldList) {
            if (fieldValidator(propertyNames, df)) {
                const dataField = new DataField(df[propertyNames.at(0)],
                    df[propertyNames.at(1)],
                    df[propertyNames.at(2)],
                    df[propertyNames.at(3)],
                    df[propertyNames.at(4)],
                    df[propertyNames.at(5)],
                    df[propertyNames.at(6)],
                    df[propertyNames.at(7)],
                    df[propertyNames.at(8)]);
                dataFields.push(dataField);
            } else {
                alert("Data Retrieval Failed.")
                return;
            }
        }
        return dataFields;
    }
}

/**
 * Method to parse the Sections that are sent as a list in the server response entity.
 * @param sectionList of type Section[].
 */
export function parseSections(sectionList) {
    const sections = [];
    if (sectionList.length === 0) {
        invalidSearch();
    } else {
        let propertyNames = Object.keys(sectionList[0]);
        for (const sec of sectionList) {
            if (fieldValidator(propertyNames, sec)) {
                const sect = new Section(sec[propertyNames.at(0)],
                    sec[propertyNames.at(1)],
                    sec[propertyNames.at(2)],
                    sec[propertyNames.at(3)]);
                sections.push(sect);
                console.log("Section Validated");
            }
        }
    }
    return sections;
}

// FETCH() -------------------------------------------------------------------------------------------------------------------------------------

/**
 * This method is used to construct the URI for the fetch.
 * @param selectedRegistration of type Registration.
 * @returns {string} being the URI.
 */
export function buildRegistrationURI(selectedRegistration) {
    let URI = "./api/registrations/";
    switch(selectedRegistration.registration_id) {
        case "" || null:
            invalidSearch();
            return "NONE";
        default:
            URI += selectedRegistration.registration_id + "/fields";
    }
    return URI;
}

/**
 * Uses fetch() to get the RegistrationContainer from the back-end, and parse it using JSON.
 */
async function queryDetails() {
    clearDiv(document.getElementById("content_space"));
    let URI = "./api/registrations/";
    switch(sReg.registration_id) {
        case "" || null:
            invalidSearch();
            return;
        default:
            URI += sReg.registration_id + "/fields";
    }
    console.log("The URI is: " + URI);
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
                const reg = parseRegistration(container.reg);
                savedReg = reg;
                const dfs = parseDataFields(container.df_pos);
                savedFields = dfs;
                const sects = parseSections(container.sections);
                savedSections = sects;
                console.log("Before");
                populatePage(reg, dfs, sects);
                document.getElementById("registration-form").dataset.status = reg.status;
                await queryModifications();
                await(queryStyles(sReg.registration_id, savedReg.registrationFormID, "content_space", "content-input", "section-name"));
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
 * This method is used to query the modification records for a particular registration.
 * @returns {Promise<void>}
 */
async function queryModifications() {
    let URI = "./api/registrations/" + sReg.registration_id + "/modificationsForParent";
    try {
        const response = await fetch(URI);
        if (!response.ok) {
            throw new Error("Could not establish connection with database.");
        }
        const modifications_list = await response.json();
        if (modifications_list !== null && modifications_list !== undefined) {
            const mods = parseModificationViews(modifications_list);
            organizeModifications(mods, false, document.getElementById("content_space"));
        }
    } catch (Error) {
        alert("Something went wrong.")
    }
}

/**
 * This method is used to organize the modifications in a presentable list to the viewer.
 * @param mods_list
 * @param visible
 * @param container
 */
function organizeModifications(mods_list, visible, container) {
    mods_list.forEach(mod => {
        const dv = document.createElement("div");
        /**/
        dv.setAttribute("class", "mod");
        /**/
        dv.setAttribute("id", "modBox");
        dv.innerHTML = "<p>Date Posted: " + mod.date + "</p><br>" +
            "<p>Admin Surname: " + mod.surname + "</p><br>" +
            "<p>Description: " + mod.description + "</p>";
        if (visible) {
            dv.innerHTML += "<br><p>Visibility: " + mod.visible + "</p>";
        }
        container.appendChild(dv);
    });
    return container;
}

/**
 * Executes DELETE request to the registration, requiring just the registration_id. If not permissible (based on ENUM Status),
 * client will be informed. Redirects user to the dashboard.
 */
async function deleteRegistration() {
    let URI = "./api/registrations/" + sReg.registration_id;
    console.log("The URI is: " + URI);
    if (invalidDeletionStatus.includes(sReg.registration_id + "")) {
        alert("You are not permitted to delete the registration in this status. Please request assistance with " +
            "the school administrator.");
    }
    try {
        const response = await fetch(URI, {method: "DELETE"});
        if (!response.ok) {
            throw new Error("Registration Details Unavailable At This Time!");
        } else {
            alert("Deletion was successful.");
        }
    } catch (Error) {
        alert("Something went wrong with the deletion. We urge you to try again later.");
    }
}

/**
 * A list is saved of the fields as they arrive, this list is preserved and updated with each save request. Thus, if an
 * edit is cancelled, the previous save is maintained, and the form returns to view mode.
 */
function cancelChanges() {
    sessionStorage.setItem("pageStatus", PageStatus.ViewOnly.returnName());
    alert("Your changes will not be saved.");
    returnToDashboard();
}

/**
 * This method is used to submit the data from the registration.
 * @returns {Promise<void>}
 */
async function submitRegistration() {
    // Send the updated status of the registration, then send the updated fields.
    if (sReg.status === "AWAITING_SUBMISSION" || sReg.status === "MODIFICATIONS_ALLOWED") {
        try {
            const update = new RegistrationUpdate(sReg.registration_id, "SUBMITTED");
            let URI = "./api/registrations/" + sReg.registration_id;
            const response = await fetch(URI, {
                headers: {
                    "Content-Type": "application/json"
                },
                method: "PUT",
                body: JSON.stringify(update)
            });
            if (!response.ok) {
                throw new Error("Process not Possible")
            }
            const reg = await response.json();
            alert("Your submission was successful.");
            returnToDashboard();
        } catch (Error) {
            alert("Unsuccessful, please try again later.");
        }
    }
}

/**
 * This method is used to save the data for a registration.
 * @returns {Promise<void>}
 */
async function saveRegistration() {
    // Send the updated status of the registration, then send the updated fields.
    if (sReg.status === "AWAITING_SUBMISSION" || sReg.status === "MODIFICATIONS_ALLOWED") {
        try {
            const update = new RegistrationUpdate(sReg.registration_id, sReg.status);
            let URI = "./api/registrations/" + sReg.registration_id;
            const response = await fetch(URI, {
                headers: {
                    "Content-Type": "application/json"
                },
                method: "PUT",
                body: JSON.stringify(update)
            });
            if (!response.ok) {
                throw new Error("Process not Possible")
            }
            const reg = await response.json();
        } catch (Error) {
            alert("Unsuccessful, please try again later.");
        }
    }
}

/**
 * This method is used to process the files to be sent to the server.
 * @returns {Promise<void>}
 */
async function processFiles() {
    const data = parseBytesToBlob();
    alert("File Sending Awaiting Implementation");

}

/**
 * This method is used to parse the bytes from the file to a Blob object to send to the back-end.
 * @returns {FormData}
 */
function parseBytesToBlob() {
    const formData = new FormData();
    fileByteArrayContainer.forEach((byteArray, indexPos) => {
        const blob = new Blob(byteArray, {type: "application/octet-stream"});
        formData.append(`file_${indexPos}`, blob);
    });
    return formData;
}

/**
 * Executes the two queries: updating status of registration, updating the fields. Then, it redirects the client to the dashboard (or return to view mode).
 * Collect the fields from the page, build the field objects with the updated content, and ship them to the back-end.
 */
async function saveChanges(submit) {
    const fieldsInSpan = getFieldContainers();
    const fieldsToSave = updateValues(fieldsInSpan);
    const fieldsToSend = [];
    for (const field of fieldsToSave) {
        /** @type {DataField} */
        const dataField = field;
        fieldsToSend.push(new BEDataField(dataField.fieldID, dataField.registrationID, dataField.content));
    }
    if (fieldsToSend.length === savedFields.length) {
        let URI = "./api/registrations/" + sReg.registration_id + "/fields";
        if (submit === true) {
            await submitRegistration();
        } else {
            await saveRegistration();
        }
        try {
            const response = await fetch(URI, {
                headers: {
                    "Content-Type": "application/json"
                },
                method: "PUT",
                body: JSON.stringify(fieldsToSend)
            });
            if (!response.ok) {
                throw new Error("Database is inaccessible");
            }
            const dfList = await response.json();
            alert("Your update was successful.");
            returnToDashboard();
        } catch (Error) {
            alert("Something went wrong.");
            returnToDashboard();
        }
    } else {
        alert("Something went wrong.");
        returnToDashboard();
        console.log("Sizes are different. Size of savedFields: " + savedFields.length + " | size of pending fields: " + fieldsToSend.length);
    }
}

/**
 * Method used to update the values of the data fields.
 * @param fieldsInSpan
 * @returns {DataField[]}
 */
function updateValues(fieldsInSpan) {
    const fieldsToSave = [];
    const inputs = document.getElementsByClassName("content-input");
    for (const input of inputs) {
        savedFields.forEach(field => {
            /** @type {DataField} */
            const df = field;
            if (df.title === input.dataset.componentTitle) {
                let value = input.value;
                if (df.dataType === "File" || df.dataType === "Image") {
                    value = input.files[0];
                    if (validateDataField(value, df.dataType, df.title)) {
                        const reader = new FileReader();
                        reader.onload = function(event) {
                            const data = event.target.result;
                            const arr = new Uint8Array(data);
                            const bytes = Array.from(arr);
                            fileByteArrayContainer.push(bytes);
                        }
                        reader.readAsArrayBuffer(value);
                        df.content = value.name; // Assign file name, later to be converted to proper path on back-end.
                        fieldsToSave.push(df);
                    } else {
                        alert("Invalid File Upload");
                        return fieldsToSave;
                    }
                } else {
                    if (validateDataField(value, df.dataType, df.title)) {
                        df.content = value;
                        fieldsToSave.push(df);
                    } else {
                        alert("Invalid Field");
                        return fieldsToSave;
                    }
                }
            }
        });
    }
    return fieldsToSave;
}

/**
 * Method used to get the containers for the data fields on the form.
 * @returns {HTMLCollectionOf<Element>}
 */
function getFieldContainers() {
    return document.getElementsByClassName("field");
}

// STATUS CHANGE METHOD(S) ---------------------------------------------------------------------------------------------------------------------------------

/**
 * Method used to change the mode of the form.
 */
function setUpEditingMode() {
    pStatus.length = 0;
    sessionStorage.setItem("pageStatus", PageStatus.Editable.returnName());
    alert("The page will be refreshed.");
    window.location.href = "/Topicus/viewRegistrationParent.html";
}

/**
 * Method after save/deletion, to return to the dashboard.
 */
function returnToDashboard() {
    window.location.href = "/Topicus/dashboard.html";
}
// FORM-BUILDING METHOD(S) ----------------------------------------------------------------------------------------------------------------------------------

/**
 * Used to construct a section from the form.
 * @param sectionName represents the name of the section.
 * @returns {string}
 */
export function sectionBuilder(sectionName) {
    return " <p class='section-name'>" + sectionName + "</p> ";
}

/**
 * Used to construct the field of a form.
 * @param title representing the title.
 * @param content representing the content.
 * @param mandatory
 * @param dataType
 * @returns {string}
 */
function formFieldBuilder(title, content, mandatory, dataType) {
    const arr = generateMandatoryDTStrings(mandatory, dataType);
    if (pStatus[0] === PageStatus.ViewOnly.returnName()) {
        return formFieldGenerator(title, content, mandatory, dataType, true).outerHTML;
    } else {
        return formFieldGenerator(title, content, mandatory, dataType, false).outerHTML;
    }
}

/**
 * Method to create the fields in the event that a form is view-only.
 * @param title of type String.
 * @param content of type String.
 * @param mandatory
 * @param dataType
 * @returns {string} of type String.
 */
export function viewFields(title, content, mandatory, dataType) {
    const arr = generateMandatoryDTStrings(mandatory, dataType);
    return formFieldGenerator(title, content, mandatory, dataType, true).outerHTML;
}

/**
 * Used to construct the form to be displayed on the front-end.
 * @param content representing inner details of the form.
 * @returns {string}
 */
export function formBuilder(content) {
    return "<form id='registration-form' action='#' method='get'> " + content + "</form>";
}

/**
 * This method will be used to produce the form on the page.
 * @param reg of type Registration.
 * @param dfs of type [DataField]
 * @param sects of type [Section]
 */
function populatePage(reg, dfs, sects) {
    let body = "";
    body += "<p><h3>Current Status: " + reg["status"].replace("_", " ") + "</h3></p>";
    // const sortedSections = sortList(sects, "position");
    const sortedSections = sects.sort((s1, s2) => (s1["position"] > s2["position"]) ? 1 : (s1["position"] < s2["position"]) ? -1 : 0);
    // const sortedDataFields = sortList(dfs, "position");
    const sortedDataFields = dfs.sort((d1, d2) => (d1["position"] > d2["position"]) ? 1 : (d1["position"] < d2["position"]) ? -1 : 0)
    for(const section of sortedSections) {
        console.log("SECTION: " + JSON.stringify(section));
        body += sectionBuilder(section["title"]);
        for (const dataf of sortedDataFields) {
            console.log("DATA FIELD " + JSON.stringify(dataf));
            if (dataf["sectionID"] === section["sectionID"]) {
                body += formFieldBuilder(dataf["title"], dataf["content"], dataf["mandatory"], dataf["dataType"]);
            }
        }
    }
    let buttons = generateButtons();
    body += buttons;
    console.log(body);
    let finalForm = formBuilder(body);
    console.log(finalForm);
    document.getElementById("content_space").innerHTML = finalForm;
    initializeButtons();
}

/**
 * Method used to generate the buttons, will also account for the additional buttons of SUBMIT (given that status is not SUBMITTED or any other afterwards).
 * @returns {string}
 */
function generateButtons() {
    let output = "";
    if (pStatus[0] === PageStatus.ViewOnly.returnName()) {
        output += "<button id='back-button'>Back</button> ";
        output += "<button id='delete-button'>Delete</button>";
        if (!invalidEditingStatus.includes(sReg.status)) {
            console.log("Edit added");
            output += "<button id='edit-button'>Edit</button>";
        }
    } else {
        output += "<button id='cancel-button'>Cancel</button> ";
        output += "<button id='save-button'>Save</button>";
        if (submissionButtonCriteria.includes(sReg.status)) {
            output += "<button id='submit-button'>Submit</button>"
        }
    }
    return output;
}

/**
 * Method used to add event listeners to the buttons to make them functional.
 */
function initializeButtons() {
    switch(pStatus[0]) {
        case PageStatus.ViewOnly.returnName():
            const deleteButton = document.getElementById("delete-button");
            const backButton = document.getElementById("back-button");
            deleteButton.addEventListener("click", async function(e) {
                e.preventDefault();
                await deleteRegistration();
            });
            backButton.addEventListener("click", function(e) {
                e.preventDefault();
                window.location.href = "/Topicus/dashboard.html";
            })
            if (!invalidEditingStatus.includes(sReg.status)) {
                console.log("Added functionality");
                const editButton = document.getElementById("edit-button");
                editButton.addEventListener("click", function(e) {
                    e.preventDefault();
                    setUpEditingMode();
                });
            }
            break;
        case PageStatus.Editable.returnName():
            const cancelButton = document.getElementById("cancel-button");
            const saveButton = document.getElementById("save-button");
            cancelButton.addEventListener("click", function(e) {
                e.preventDefault();
                cancelChanges();
            });
            saveButton.addEventListener("click", async function(e) {
                e.preventDefault();
                await saveChanges(false);
            });
            if (submissionButtonCriteria.includes(sReg.status)) {
                const submitButton = document.getElementById("submit-button");
                submitButton.addEventListener("click", async function(e) {
                    e.preventDefault();
                    await submitRegistration();
                });
            }
            break;
    }
}