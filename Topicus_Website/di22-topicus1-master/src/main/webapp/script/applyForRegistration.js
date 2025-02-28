import { get, post } from "./requests.js";
import { getSessionGuardianID, hasSession, isLoggedInWithAccountAndData, sessionWithGID } from "./storageManagement.js";
import { inputSanitizer, isEmpty } from "../fe_security/inputsanitizer.js";
import {validateDateFormat, applyStyles} from './formUtils.js';

const urlParams = new URLSearchParams(window.location.search);
const school_id_param = urlParams.get('school_id');
const registration_form_id_param = urlParams.get('form_id');

const school_id = sessionStorage.getItem('selectedSchool');
const registration_form_id = sessionStorage.getItem('selectedRegistrationForm');

//check if school_id and registration_form_id are null
if (school_id === null || registration_form_id === null) {
    //check if school_id and registration_form_id are in url
    if (school_id_param !== null && registration_form_id_param !== null) {
        sessionStorage.setItem('selectedSchool', school_id_param);
        sessionStorage.setItem('selectedRegistrationForm', registration_form_id_param);
        window.location.href = window.location.href.split('?')[0];
    } else {
        window.location.href = "/Topicus/";
    }
}

let BEDataFields = [];
let registration_id = undefined;

const address = { //mandatory contents - 6 on form
    "postalCode": "",
    "streetName": "",
    "streetNumber": "", //number
    "city": "",
    "country": "",
    "phoneNumber": ""
};

let guardian = { //mandatory contents - 7 on form
    "address_id": "",
    "nationality": "",
    "surname": "",
    "given_names": [],
    "phone_number": "",
    "birth_date": "1989-09-01",
    "occupation": "",
    "company_name": ""
    // extra fields . . .
};

let child = { //mandatory contents - 7 on form
    "guardianId": "",
    "surname": "",
    "givenNames": [],
    "preferredName": "",
    "birthDate": 0,
    "bsn": "",
    "nationality": "",
    "languages": []
    // extra fields . . .
};

/**
 *  RegistrationFormMetaData class
 */

let style = null;
class RegistrationFormMetaData {
    constructor(registration_form_id, school_id, title, description, year, education_type, is_deleted, is_active, start_date) {
        this.registration_form_id = registration_form_id;
        this.school_id = school_id;
        this.title = title;
        this.description = description;
        this.year = year;
        this.education_type = education_type;
        this.is_deleted = is_deleted;
        this.is_active = is_active;
        this.start_date = start_date;
    }
}

/**
 * FormComponent class
 */
class FormComponent {
    constructor(form_component_id, registration_form_id, section_id, position, title, mandatory, data_type) {
        this.form_component_id = form_component_id;
        this.registration_form_id = registration_form_id;
        this.section_id = section_id;
        this.position = position;
        this.title = title;
        this.mandatory = mandatory; // true | false
        this.data_type = data_type; // text, number, date, image, file
    }
}

/**
 * Section class
 */
class Section {
    constructor(section_id, registration_form_id, position, title) {
        this.section_id = section_id;
        this.registration_form_id = registration_form_id;
        this.position = position;
        this.title = title;
    }
}

/**
 * SectionContainer class
 */
class SectionContainer {
    constructor(section, formComponents) {
        this.section = section;
        this.formComponents = formComponents;
    }
}

/**
 * Load the Registration Form when the page loads - put in 
 */
window.addEventListener("load", async function () {
    await getGuardianData();
    await queryForm(school_id, registration_form_id);
});

/**
 * @GET guardian and their address.
 * @returns {Promise<void>}
 */
async function getGuardianData() {
    if (sessionWithGID() || isLoggedInWithAccountAndData()) {
        const guardian_id = getSessionGuardianID();
        const URI = `./api/parents/${guardian_id}`;
        guardian = await get(URI);
        address["addressID"] = guardian.address_id;
    }
}

/**
 * Method for parsing the registration form
 * @param registrationForm the registration form
 * @returns {RegistrationFormMetaData} the parsed registration form
 */
function parseRegistrationForm(registrationForm) {
    const registrationFormKeys = Object.keys(registrationForm);
    return new RegistrationFormMetaData(registrationForm[registrationFormKeys.at(0)], registrationForm[registrationFormKeys.at(1)], registrationForm[registrationFormKeys.at(2)], registrationForm[registrationFormKeys.at(3)], registrationForm[registrationFormKeys.at(4)], registrationForm[registrationFormKeys.at(5)], registrationForm[registrationFormKeys.at(6)], registrationForm[registrationFormKeys.at(7)], registrationForm[registrationFormKeys.at(8)], registrationForm[registrationFormKeys.at(9)]);
}

/**
 * Method for parsing a form component
 * @param formComponent the form component
 * @returns {FormComponent} the parsed form component
 */
function parseFormComponent(formComponent) {
    const formComponentKeys = Object.keys(formComponent);
    return new FormComponent(formComponent[formComponentKeys.at(0)], formComponent[formComponentKeys.at(1)], formComponent[formComponentKeys.at(2)], formComponent[formComponentKeys.at(3)], formComponent[formComponentKeys.at(4)], formComponent[formComponentKeys.at(5)], formComponent[formComponentKeys.at(6)], formComponent[formComponentKeys.at(7)]);
}

/**
 * Method for parsing the form components
 * @param formComponents the form components
 * @returns {Array} the parsed form components
 */
function parseFormComponents(formComponents) {
    const parsedFormComponents = [];
    for (const formComponent of formComponents) {
        parsedFormComponents.push(parseFormComponent(formComponent));
    }
    return parsedFormComponents;
}

/**
 * Method for parsing a section
 * @param section the section
 * @returns {Section} the parsed section
 */
function parseSection(section) {
    const sectionKeys = Object.keys(section);
    return new Section(section[sectionKeys.at(0)], section[sectionKeys.at(1)], section[sectionKeys.at(2)], section[sectionKeys.at(3)]);
}

/**
 * Method for parsing the section containers
 * @param sectionContainers the section containers
 * @returns {Array} the parsed section containers
 */
function parseSectionContainers(sectionContainers) {
    const parsedSectionContainers = [];
    for (const sectionContainer of sectionContainers) {
        const section = parseSection(sectionContainer["section"]);
        const formComponents = parseFormComponents(sectionContainer["formComponentList"]);
        parsedSectionContainers.push(new SectionContainer(section, formComponents));
    }
    return parsedSectionContainers;
}

/**
 * Query the database for the registration form
 */
async function queryForm(school_id, registration_form_id) {
    const URI = `./api/schools/${school_id}/forms/${registration_form_id}`;
    const registrationFormContainer = await get(URI);

    if (registrationFormContainer !== null && registrationFormContainer !== undefined) {
        if (registrationFormContainer["formMetadata"] !== null && registrationFormContainer["formMetadata"] !== undefined) {
            const registrationForm = parseRegistrationForm(registrationFormContainer["formMetadata"]);
            const sectionContainers = parseSectionContainers(registrationFormContainer["sectionContainerList"]);
            style = registrationFormContainer.formStyle;
            await populateRegistrationForm("guardian", registrationForm, sectionContainers, sectionContainers);
        }
    }
    else {
        alert('Something went wrong with the loading of the form!\nPlease, try again or proceed with another form!');
        throw new Error('ouch');
    }
}

/**
 * Loads Preview page.
 * @param {*} registrationForm 
 * @param {*} sectionContainers 
 */
async function populatePreviewForm(registrationForm, sectionContainers) {
    createFormElement();
    await populateRegistrationFormDetails('preview', registrationForm);
    populateSections('preview', sectionContainers);
    populateFooterButtons('preview', registrationForm, sectionContainers);
    populateInfo('preview');
}

/**
 * Populate the registration form
 * @param details - guardian / child / other
 * @param registrationForm the registration form
 * @param sectionContainers the section containers
 * @param originalSectionContainers
 */
async function populateRegistrationForm(details, registrationForm, sectionContainers, originalSectionContainers) { //populate page depending on details
    if (sectionContainers[0].formComponents === null || sectionContainers[0].formComponents === undefined) {
        alert('It appears that the school has not yet finished creating this form.\nPlease choose another form or school.');
        window.location.href = "/Topicus/schools.html";
    } else {
        createFormElement();
        let updatedSectionContainers = [];
        if (details === "guardian" || details === "child") {
            for (let i = 0; i < sectionContainers.length; i++) {
                if ((details === "guardian" && sectionContainers[i].section.position === 1)) {
                    updatedSectionContainers.push(sectionContainers[i]);
                    originalSectionContainers.unshift(sectionContainers[i]); // A hidden connection between originalSectionContainers and sectionContainers occurred which could not be resolved in any other way
                    sectionContainers.splice(i, 1);
                    break;
                } else if (details === "child" && sectionContainers[i].section.position === 2) {
                    updatedSectionContainers.push(sectionContainers[i]);
                    originalSectionContainers.splice(1, 0, sectionContainers[i]); // A hidden connection between originalSectionContainers and sectionContainers occurred which could not be resolved in any other way
                    sectionContainers.splice(i, 1);
                    break;
                }
            }
        } else {
            updatedSectionContainers = sectionContainers.slice(2);
            originalSectionContainers.push(...sectionContainers);
            originalSectionContainers.splice(originalSectionContainers.length / 2);
        }

        await populateRegistrationFormDetails(details, registrationForm);
        populateSections(details, updatedSectionContainers);
        populateFooterButtons(details, registrationForm, updatedSectionContainers, sectionContainers, originalSectionContainers);
        populateInfo(details);
        applyStyles(style, "registration-form-field-set", "form-component-input", "section-attribute-to-style");
    }
}

/**
 * Create the form element
 * @returns {HTMLFormElement} the form element
 */
function createFormElement() {
    const formFieldSet = document.getElementById("registration-form-field-set");
    formFieldSet.innerHTML = "";
    const formElement = document.createElement("form");
    formElement.setAttribute("id", "registration-form");
    formElement.setAttribute("action", "#");
    formElement.setAttribute("method", "post");
    formFieldSet.appendChild(formElement);
}

/**
 * Populate the registration form details
 * @param details
 * @param registrationForm the registration form
 */
async function populateRegistrationFormDetails(details, registrationForm) {
    const registrationFormElement = document.getElementById("registration-form");
    //Create title. Can also be created with createRegistrationFormDetails.
    const registrationFormTitle = document.createElement("h1");
    let dropdown = undefined;
    if (details === "guardian") {
        registrationFormTitle.innerText = "Guardian Details";
    } else if (details === "child") {
        registrationFormTitle.innerText = "Child Details";

        const appliedChildren = await getChildrenByGuardian();
        if (appliedChildren !== undefined) {
            dropdown = createChildrenDropdown(appliedChildren);
        }

    } else if (details === "preview") {
        registrationFormTitle.innerText = `Preview\n${registrationForm.title}`;
    } else {
        registrationFormTitle.innerText = registrationForm.title;
    }

    registrationFormElement.appendChild(registrationFormTitle);
    if (dropdown !== undefined) {
        registrationFormElement.appendChild(dropdown);
    }
    //MAYBE ADD THAT LATER
    //registrationFormElement.appendChild(createRegistrationFormDetails(registrationForm));
}

// ----- CHILD SELECTION -----
/**
 * Creates a dropdown element on the Child Details form and loads it with the names of all children related to that guardian.
 * @param {object} appliedChildren 
 * @returns {HTMLSpanElement} which contains the dropdown feature
 */
function createChildrenDropdown(appliedChildren) {
    const dropdown = document.createElement("span");
    dropdown.setAttribute("id", "dropdown");
    const label = document.createElement("label");
    label.setAttribute("for", "child");
    label.innerText = "Registering a child again? Select here:";
    dropdown.appendChild(label);
    dropdown.appendChild(createDropDownOptions(appliedChildren));
    return dropdown;
}

function createDropDownOptions(appliedChildren) {
    const selectBlock = document.createElement("select");
    selectBlock.setAttribute("id", "child");
    selectBlock.addEventListener('change', function (event) {
        updateForm(event, this.value);
    });

    for (const appliedChild of appliedChildren) {
        const option = document.createElement("option");
        option.value = appliedChild.childID;
        option.textContent = appliedChild.givenNames.join(' ') + ' ' + appliedChild.surname;
        selectBlock.appendChild(option);
    }
    const lastOption = document.createElement("option");
    lastOption.value = "unset";
    lastOption.textContent = "Add new child";
    lastOption.selected = true;
    selectBlock.appendChild(lastOption);
    return selectBlock;
}

/**
 * Updates the form fields the guardian makes their choice with a little timeout between change of choices.
 */
function updateForm(event, value) {
    event.preventDefault();
    const selectBlock = document.getElementById('child');
    if (value === "unset") {
        resetChild();
        hideMandatoryChildFields(false);
    } else {
        hideMandatoryChildFields(true);
        selectBlock.disabled = true;
        setTimeout(function () {
            // Unlock the selectBlock element after 500ms
            selectBlock.disabled = false;
        }, 500);
    }
}

async function setChild() {
    const selectBlock = document.getElementById('child');
    if (selectBlock !== null && selectBlock !== undefined) {
        const childID = selectBlock.options[selectBlock.selectedIndex].value;
        if (childID !== "unset" && childID !== undefined && child !== null) {
            child = await getChildByID(childID);
        }
    }
}

/**
 * Resets child object.
 */
function resetChild() {
    child = {
        "guardianId": "",
        "surname": "",
        "givenNames": [],
        "preferredName": "",
        "birthDate": "",
        "bsn": 0,
        "nationality": "",
        "languages": []
    };
}

// ------- Continue with form population --------

/**
 * Hides the mandatory Child Details fields if a parent chooses to apply a child again.
 * @param {boolean} hide 
 */
function hideMandatoryChildFields(hide) {
    const formComponents = document.getElementsByClassName('form-component');
    for (let i = 0; i <= 6; i++) {
        if (hide) {
            formComponents[i].style.display = 'none';
        } else {
            formComponents[i].style.display = 'block';
        }
    }
}
// -------

/**
 * Create the registration form details
 * @param registrationForm the registration form
 * @returns {HTMLDivElement} the registration form details
 */
function createRegistrationFormDetails(registrationForm) {
    //Moved the creation of title in populateRegistrationFormDetails
    const registrationFormDetails = document.createElement("div");
    registrationFormDetails.setAttribute("id", "registration-form-details");
    registrationFormDetails.appendChild(createRegistrationFormField("title", registrationForm.title));
    //MAYBE ADD THESE LATER
    //registrationFormDetails.appendChild(createRegistrationFormField("description", registrationForm.description));
    //registrationFormDetails.appendChild(createRegistrationFormField("year", registrationForm.year));
    //registrationFormDetails.appendChild(createRegistrationFormField("education_type", registrationForm.education_type));
    return registrationFormDetails;
}

/**
 * Create the registration form details field
 * @param fieldName the field name
 * @param fieldValue the field value
 * @returns {HTMLDivElement} the registration form field
 */
function createRegistrationFormField(fieldName, fieldValue) {
    const registrationFormField = document.createElement("div");
    registrationFormField.setAttribute("id", "registration-form-" + fieldName);
    registrationFormField.innerText = fieldValue;
    return registrationFormField;
}

/**
 * Populate the sections
 * @param details
 * @param sectionContainers the section containers
 */
function populateSections(details, sectionContainers) {
    sectionContainers[0].formComponents.sort((a, b) => a.position - b.position);
    const registrationFormElement = document.getElementById("registration-form");
    const createdSection = createSections(details, sectionContainers);
    if (createdSection !== null) {
        registrationFormElement.appendChild(createdSection);
    }
}

/**
 * Create the sections
 * @param details
 * @param sectionContainers the section containers
 * @returns {HTMLDivElement} the sections
 */
function createSections(details, sectionContainers) {
    const sections = document.createElement("div");
    sections.setAttribute("id", "sections");
    const orderedSectionContainers = sectionContainers.sort((a, b) => a.section.position - b.section.position);
    if (details === "guardian" && hasSession()) {
        const sectionContainer = orderedSectionContainers[0];
        if (sectionContainer.formComponents.length === 7) {
            return null;
        } else {
            if (sectionContainer.formComponents.length > 7) {
                const spliced = sectionContainer.formComponents.splice(0, 7);
                sections.appendChild(createSection(details, sectionContainer, 1, 0));
                sectionContainer.formComponents.unshift(...spliced);
            } else {
                sections.appendChild(createSection(details, sectionContainer, 1, 0));
            }
        }
    } else {
        for (let i = 0; i < orderedSectionContainers.length; i++) {
            const sectionContainer = orderedSectionContainers[i];
            if (hasSession() && details === 'preview' && (i === 0 || (i === 1 && child.childID))) {
                if (sectionContainer.formComponents.length > 7) {
                    const spliced = sectionContainer.formComponents.splice(0, 7);
                    sections.appendChild(createSection(details, sectionContainer, orderedSectionContainers.length, i));
                    sectionContainer.formComponents.unshift(...spliced);
                }
            } else {
                sections.appendChild(createSection(details, sectionContainer, orderedSectionContainers.length, i));
            }
        }
    }
    return sections;
}

/**
 * Create a section
 * @param details
 * @param sectionContainer the section container
 * @param numSections
 * @param countCreatedSections
 * @returns {HTMLDivElement} the section
 */
function createSection(details, sectionContainer, numSections, countCreatedSections) {
    const section = document.createElement("div");
    section.setAttribute("id", "section-" + sectionContainer.section.position);
    section.setAttribute("class", "section");
    if (numSections > 1) {
        section.appendChild(createSectionTitle(sectionContainer.section));
    }
    section.appendChild(createSectionFormComponents(details, sectionContainer.formComponents, countCreatedSections));
    return section;
}

/**
 * Create the section title
 * @param section the section
 * @returns {HTMLHeadingElement} the section title
 */
function createSectionTitle(section) {
    const sectionDetails = document.createElement("h2");
    sectionDetails.setAttribute("class", "section-attribute-to-style");
    sectionDetails.innerText = section.title;
    return sectionDetails;
}

/**
 * Create the section form components
 * @param details
 * @param formComponents the form components
 * @param countCreatedSections
 * @returns {HTMLDivElement} the section form components
 */
function createSectionFormComponents(details, formComponents, countCreatedSections) {
    const sectionFormComponents = document.createElement("div");
    sectionFormComponents.setAttribute("class", "section-form-components");

    // Append the address formComponents in the beginning of Guardian Details or in Preview only to section Guardian Details
    if ((details === 'guardian' && !hasSession()) || (details === 'preview' && countCreatedSections === 0 && !hasSession())) {
        for (let i = 0; i < Object.entries(address).length; i++) {
            const addressComponent = Object.entries(address)[i];
            sectionFormComponents.appendChild(createAddressFormComponent(addressComponent, i));
        }
    }

    const orderedFormComponents = formComponents.sort((a, b) => a.position - b.position);
    for (const formComponent of orderedFormComponents) {
        sectionFormComponents.appendChild(createFormComponent(formComponent));
    }

    return sectionFormComponents;
}

/**
 * Create a form component
 * @param formComponent the form component
 * @returns {HTMLSpanElement} the form component
 */
function createFormComponent(formComponent) {
    const formComponentElement = document.createElement("span");
    formComponentElement.setAttribute("id", "form-component-" + formComponent.position);
    formComponentElement.setAttribute("class", "form-component");
    formComponentElement.appendChild(createFormComponentLabel(formComponent));
    formComponentElement.appendChild(createFormComponentInput(formComponent));
    return formComponentElement;
}

/**
 * Create a form component ONLY for the address details
 * @param addressComponent the address form component
 * @param {number} i
 * @returns {HTMLSpanElement} the address form component
 */
function createAddressFormComponent(addressComponent, i) {
    const formComponentElement = document.createElement("span");
    formComponentElement.setAttribute("id", "address-form-component-" + (i + 1));
    formComponentElement.setAttribute("class", "address-form-component");
    // Make the address component in appropriate format
    let title = addressComponent[0] // get the name of the key of the entry
    title = title.substring(0, 1).toUpperCase() + title.substring(1); // capitalize first letter
    title = title.split(/(?=[A-Z])/).join(' '); // split in separate words by capital letters and add spaces

    const formattedComponent = { title };
    formComponentElement.appendChild(createFormComponentLabel(formattedComponent));
    formComponentElement.appendChild(createFormComponentInput(formattedComponent, i));
    return formComponentElement;
}

/**
 * Create the form component label
 * @param formComponent the form component
 * @returns {HTMLLabelElement} the form component label
 */
function createFormComponentLabel(formComponent) {
    const formComponentLabel = document.createElement("label");
    formComponentLabel.setAttribute("class", "form-component-label");
    formComponentLabel.setAttribute("for", formComponent.title);
    formComponentLabel.innerText = formComponent.title;
    return formComponentLabel;
}

/**
 * Create the form component input
 * @param formComponent the form component
 * @param i - only for addressFormComponents - to index them correctly
 * @returns {HTMLInputElement} the form component input
 */
function createFormComponentInput(formComponent, i) {
    const formComponentInput = document.createElement("input");
    formComponentInput.setAttribute("class", "form-component-input");
    formComponentInput.setAttribute("type", "text");
    formComponentInput.setAttribute("name", formComponent.title + ":");
    formComponentInput.placeholder = formComponent.title;
    fillFormComponentInput(formComponent, formComponentInput, i);
    return formComponentInput;
}

/**
 * Executes only for Preview page - loads the data in the fields.
 * @param {object} formComponent the form component
 * @param {HTMLInputElement} formComponentInput 
 * @param {number} i the index of the formComponent on the page
 */
function fillFormComponentInput(formComponent, formComponentInput, i) {
    if (i !== undefined) { //put extra fields in objects as well just delete them
        formComponentInput.value = Object.values(address)[i];
    } else {
        for (const detail of BEDataFields) {
            if (detail["component_id"] === formComponent.form_component_id) {
                formComponentInput.value = detail["content"];
            }
        }
    }
}

/**
 * Populate the footer buttons.
 * @param {string} details 
 * @param {object} registrationForm 
 * @param {object} updatedSectionContainers 
 * @param {object} sectionContainers 
 * @param {object} originalSectionContainers 
 */
function populateFooterButtons(details, registrationForm, updatedSectionContainers, sectionContainers, originalSectionContainers) {
    const registrationFormElement = document.getElementById("registration-form");
    registrationFormElement.appendChild(createFooterButtons(details, registrationForm, updatedSectionContainers, sectionContainers, originalSectionContainers));
}

/**
 * Create buttons.
 * @param {string} details 
 * @param {object} registrationForm 
 * @param {object} updatedSectionContainers 
 * @param {object} sectionContainers 
 * @param {object} originalSectionContainers 
 * @returns {HTMLDivElement} of the button(s)
 */
function createFooterButtons(details, registrationForm, updatedSectionContainers, sectionContainers, originalSectionContainers) { // For Apply for Registration
    const footerButtons = document.createElement("div");
    footerButtons.setAttribute("id", "footer-buttons");
    const nextButton = document.createElement("a");
    const nextButtonInnerParagraph = document.createElement("p");
    nextButtonInnerParagraph.setAttribute("id", "next-button");
    nextButtonInnerParagraph.innerText = "Next";
    nextButton.appendChild(nextButtonInnerParagraph);
    footerButtons.appendChild(nextButton);
    setEventListeners(nextButton, nextButtonInnerParagraph, details, registrationForm, updatedSectionContainers, sectionContainers, originalSectionContainers);
    return footerButtons;
}

/**
 * Set the appropriate functionality and method calls to the buttons.
 * @param {HTMLAnchorElement} nextButton 
 * @param {HTMLParagraphElement} nextButtonInnerParagraph 
 * @param {string} details 
 * @param {object} registrationForm 
 * @param updatedSectionContainers
 * @param {object} sectionContainers 
 * @param {object} originalSectionContainers 
 */
function setEventListeners(nextButton, nextButtonInnerParagraph, details, registrationForm, updatedSectionContainers, sectionContainers, originalSectionContainers) {
    if (details === 'guardian') {
        nextButton.addEventListener('click',
            async function (event) {
                extractInputDataFields(event, details, updatedSectionContainers);
                await populateRegistrationForm('child', registrationForm, sectionContainers, originalSectionContainers);
            }
        );
    } else if (details === 'child') {
        nextButton.addEventListener('click',
            async function (event) {
                await setChild();
                extractInputDataFields(event, details, updatedSectionContainers);
                await populateRegistrationForm('other', registrationForm, sectionContainers, originalSectionContainers);
            }
        );
    } else if (details === 'preview') { // executes AFTER the else
        nextButtonInnerParagraph.innerText = "Apply";
        nextButton.addEventListener('click',
            async function (event) {
                extractInputDataFields(event, details, updatedSectionContainers); //updated
                await queryNewRegistration(event);
            }
        );
    } else {
        nextButton.addEventListener('click',
            async function (event) {
                extractInputDataFields(event, details, updatedSectionContainers);
                await populatePreviewForm(registrationForm, originalSectionContainers);
            }
        );
    }
}

/**
 * To be removed (when the Preview page is implemented).
 * @param {string} details - the page identifier
 */
function populateInfo(details) {
    const registrationFormElement = document.getElementById("registration-form");
    const info = document.createElement('p');
    info.setAttribute("id", "info");
    info.innerHTML = '&#9432; '; // &#9432; - HTML info symbol
    if (details === 'preview') {
        info.innerText += " Make sure all inputs are correct before proceeding!\nThis is the last step of the process!";
        info.style.display = 'block';
    } else if (details === 'guardian' && document.getElementsByTagName('input').length === 0 && hasSession()) {
        info.innerText += " All needed details by this school are already stored in your account or connected to your Guardian Code, so you can proceed.";
        info.style.display = 'block';
    } else if (details === 'guardian' && document.getElementsByTagName('input').length > 0 && hasSession()) {
        info.innerText += "Your account or Guardian Code contains all initially needed details, so you only have to input the ones particularly desired by this school.";
        info.style.display = 'block';
    } else {
        info.style.display = 'none';
    }
    registrationFormElement.appendChild(info);
}

//---------------------------------------------------------------
//---------------------------------------------------------------
//----------------------Done populating--------------------------
//---------------------------------------------------------------
//---------------------------------------------------------------

/**
 * Gets the inputs of the forms depending on the page. Use of formComponent position will have to be made
 * as every school might name the formComponents in whatever way they want to
 * @param event
 * @param {String} details
 * @param {[SectionContainer]} sectionContainers
 */
function extractInputDataFields(event, details, updatedSectionContainers) {
    event.preventDefault();
    extractAddressDetails(details);

    if (details === 'preview') {
        BEDataFields = [];
    }

    for (let i = 0; i < updatedSectionContainers.length; i++) {
        const sectionContainer = updatedSectionContainers[i];
        const sectionContainerPosition = sectionContainer.section.position;
        const count = sectionContainer.formComponents.length;

        for (let j = 0; j < count; j++) {
            const formComponent = sectionContainer.formComponents[j]; //from the fetched fields for display
            const componentID = formComponent.form_component_id;
            const componentPosition = formComponent.position;

            const contentFormComponent = setContentFormComponent(details, i, j);
            validateContentFormComponent(details, contentFormComponent, formComponent.title, formComponent.mandatory, formComponent.data_type);

            setField(details, componentPosition, contentFormComponent, sectionContainerPosition);
            const field = {
                "registration_id": '', // Set later
                "component_id": componentID,
                "content": contentFormComponent,
                "section": sectionContainerPosition, componentPosition, details
            };
            BEDataFields.push(field);
        }
    }
}

/**
 * The only component of the Registration Form which is and can be hardcoded, as schools will not be allowed to modify it.
 * @param {string} details - registration form page identifier
 */
function extractAddressDetails(details) {
    // Only for guardians without session
    if ((details === 'guardian' || details === 'preview') && !hasSession()) {
        const addressInputFields = document.getElementsByClassName('address-form-component');
        const addressAttributes = Object.keys(address);
        for (let i = 0; i < addressInputFields.length; i++) { // Can be hardcoded to i < 6
            const currentAddressInput = addressInputFields[i].childNodes[1];
            if (i === 2 && isValidInput(currentAddressInput.value, true, 'number')) {
                address[addressAttributes[i]] = currentAddressInput.value;
            } else if (isValidInput(currentAddressInput.value, true, 'text')) {
                address[addressAttributes[i]] = currentAddressInput.value;
            } else {
                displayWarningInfo(currentAddressInput.previousSibling.textContent);
            }
        }
    }
}

/**
 * Gets the content from the objects if the guardian has a session and/or has chosen a child. 
 * Gets the rest from the input fields or everything if the guardians applies for registration for the first time.
 * @param {string} details the page identifier
 * @param {number} i the section identifier
 * @param {number} j the form component identifier
 * @returns {string} the form data field to String
 */
function setContentFormComponent(details, i, j) {
    let contentFormComponent = "";
    if (hasSession() && details === 'guardian') {
        if (j <= 6) {
            const [key, value] = Object.entries(guardian)[j + 3]; //+3 because of address_id, gid, account_id
            if (key === "date_of_birth") { //Make all inputs strings as they are received with their data_types from Back-End
                contentFormComponent = formatDate(value).toString();
            } else if (key === "given_names") {
                contentFormComponent = value.join(' ');
            } else {
                contentFormComponent = value;
            }
        } else {
            contentFormComponent = document.getElementById('section-1').getElementsByClassName('form-component')[j - 7].children[1].value.trim(); // j - 7 because they do NOT exist initially
        }
    } else if (hasSession() && details === 'child') {
        if (j <= 6 && child.childID) {
            const [key, value] = Object.entries(child)[j + 1];//+1 because of guardian_id
            if (["givenNames", "languages"].includes(key)) { // typeof arrays
                contentFormComponent = value.join(' ');
            } else if (["bsn"].includes(key)) {
                contentFormComponent = value.toString();
            } else if (["birthDate"].includes(key)) {
                contentFormComponent = formatDate(value).toString();
            } else {
                contentFormComponent = value;
            }
        } else {
            contentFormComponent = document.getElementById('section-2').getElementsByClassName('form-component-input')[j].value.trim(); // j - 7 because they do NOT exist initially
        }
    } else if (hasSession() && details === 'preview') {
        if (i === 0) { //guardian details first 7 formComponents
            if (j <= 6) {
                const [key, value] = Object.entries(guardian)[j + 3]; //+3 because of address_id, gid, account_id
                if (key === "date_of_birth") { //Make all inputs strings as they are received with their data_types from Back-End
                    contentFormComponent = formatDate(value).toString();
                } else if (key === "given_names") {
                    contentFormComponent = value.join(' ');
                } else {
                    contentFormComponent = value;
                }
            } else {
                const extraGuardianDetails = document.getElementById('section-1');
                if (extraGuardianDetails !== null && extraGuardianDetails !== undefined) {
                    contentFormComponent = extraGuardianDetails.getElementsByClassName('form-component-input')[j - 7].value.trim(); // j - 7 because they do NOT exist initially
                }
            }
        } else if (i === 1) { //child details first 7 formComponents
            if (j <= 6 && child.childID) {
                const [key, value] = Object.entries(child)[j + 1];//+1 because of guardian_id
                if (["givenNames", "languages"].includes(key)) { // typeof arrays
                    contentFormComponent = value.join(' ');
                } else if (["bsn"].includes(key)) {
                    contentFormComponent = value.toString();
                } else if (["birthDate"].includes(key)) {
                    contentFormComponent = formatDate(value).toString();
                } else {
                    contentFormComponent = value;
                }
            } else {
                const extraChildDetails = document.getElementById('section-2');
                if (extraChildDetails !== null && extraChildDetails !== undefined) {
                    if (child.childID) {
                        contentFormComponent = extraChildDetails.getElementsByClassName('form-component-input')[j - 7].value.trim(); // j - 7 because they do NOT exist initially
                    } else {
                        contentFormComponent = extraChildDetails.getElementsByClassName('form-component-input')[j].value.trim();
                    }
                }
            }
        } else if (i > 1) {
            contentFormComponent = document.getElementById(`section-${i + 1}`).getElementsByClassName('form-component-input')[j].value.trim();
        }
    } else if (hasSession()) { //case for other data fields
        contentFormComponent = document.getElementById(`section-${i + 3}`).getElementsByClassName('form-component-input')[j].value.trim();
    } else {
        if (details === 'guardian' || (details === 'preview' && i === 0)) { //because of the address
            contentFormComponent = document.getElementById('section-1').getElementsByClassName('form-component')[j].children[1].value.trim();
        } else {
            contentFormComponent = document.getElementsByClassName('section')[i].getElementsByClassName('form-component-input')[j].value.trim();
        }
    }
    return contentFormComponent;
}

/**
 * Sets the values to the attributes of the corresponding object.
 * @param {string} details - the string identifier that is passed through methods to keep track of on which page the user is
 * @param {string} componentPosition - the position of the input field
 * @param {string} contentFormComponent - the extracted value of the input field
 * @param {number} sectionContainerPosition - the position of the section container
 */
function setField(details, componentPosition, contentFormComponent, sectionContainerPosition) {
    if (details === 'guardian' && componentPosition <= 7 && !hasSession() ||
        (details === 'preview' && sectionContainerPosition === 1 && componentPosition <= 7 && !hasSession())) { // 7 mandatory guardian fields

        const currentAttribute = Object.keys(guardian)[componentPosition];
        if (currentAttribute === "given_names") { // typeof array
            guardian[currentAttribute] = contentFormComponent.split(' ');
        } else {
            guardian[currentAttribute] = contentFormComponent;
        }
    }
    else if ((details === 'child' && componentPosition <= 7 && !child.childID) ||
        (details === 'preview' && sectionContainerPosition === 2 && !child.childID && componentPosition <= 7)) {

        const currentAttribute = Object.keys(child)[componentPosition]; //not -1
        if (["givenNames", "languages"].includes(currentAttribute)) { // typeof arrays
            child[currentAttribute] = contentFormComponent.split(' ');
        } else if (["bsn"].includes(currentAttribute)) {
            child[currentAttribute] = Number(contentFormComponent);
        } else {
            child[currentAttribute] = contentFormComponent;
        }
    }
}

/**
 * Validates user input by requiring non-empty inputs for mandatory fields 
 * and correct format of the data if different from text.
 * @param {string} input the user input
 * @param {boolean} mandatory determines if a field is mandatory or extra/optional
 * @param {string} data_type - text | number | date (image and file are left out)
 */
function isValidInput(input, mandatory, data_type) {
    let valid = true;
    valid = inputSanitizer(input);
    if (mandatory) {
        valid = !isEmpty(input);
    }
    if (data_type === 'NUMBER') {
        valid = !isNaN(Number(input));
    } else if (data_type === 'DATE') {
        //valid = !isNaN(Number(input)) && Object.prototype.toString.call(formatDate(input)) === "[object Date]";
        valid = validateDateFormat(input);
    }
    return valid;
}

function formatDate(timestamp) {
    const date = new Date(timestamp).toLocaleDateString('nl-NL', { day: '2-digit', month: '2-digit', year: 'numeric' });
    const date_tokens = date.split('-');
    const formatted_date = `${date_tokens[2]}-${date_tokens[1]}-${date_tokens[0]}`;
    return formatted_date;
}

function emptyFieldsByDetails(details) {
    BEDataFields = BEDataFields.filter(x => x.details !== details);
}

function validateContentFormComponent(details, contentFormComponent, formComponentTitle, mandatory, data_type) {
    if (!isValidInput(contentFormComponent, mandatory, data_type)) {
        emptyFieldsByDetails(details);
        displayWarningInfo(formComponentTitle);
    }
}

/**
 * Displays warning info to the user about their input. Can be extended to display responses to 
 * other user actions to make them more informative.
 * @param {string} componentTitle the title of the particular input field
 */
function displayWarningInfo(componentTitle) {
    const info = document.getElementById('info');
    info.style.display = 'block';
    info.innerHTML = `&#9432; `;
    info.innerText += `The input of ${componentTitle} is in invalid format or contains suspicious data!`;
    throw new Error('Invalid input!');
}

/**
 * Finalizes the application.
 * @param {Event} event
 */
async function queryNewRegistration(event) {
    event.preventDefault();
    await createGuardianAndChild();
    if (registration_id === undefined) {
        registration_id = await getRegistrationID();
    }

    const formattedBEDataFields = [];
    for (const detail of BEDataFields) {
        const formattedField = {
            "registration_id": registration_id,
            "component_id": detail["component_id"],
            "content": detail["content"]
        };
        formattedBEDataFields.push(formattedField);
    }
    const URI = `./api/registrations/${registration_id}/fields`;

    const options = {
        method: 'POST',
        headers: {}
    };

    if (formattedBEDataFields !== undefined && formattedBEDataFields !== null) {
        options.headers['Content-Type'] = 'application/json';
        options.body = JSON.stringify(formattedBEDataFields);
    }

    try {
        const response = await fetch(URI, options);
        if (response.status === 500) {
            const error = await response.json();
            alert('An invalid input was detected! Please review your data inputs!');
            throw new Error(error.message);
        } else if (!response.ok && response.status !== 204 ) {
            const error = await response.json();
            throw new Error(error.message);
        }
        await response.json();
        
    } catch (err) {
        BEDataFields = [];
        alert('Something went wrong!');
        throw err;
    }
    //await post(URI, formattedBEDataFields);
    loadGuardianID();
}

/**
 * RegistrationsResource -> @POST to create the registration and get its ID as it is needed in the BEDataField-s
 * @returns {String}
 */
async function getRegistrationID() {
    if (guardian.guardian_id && child.childID) {
        const URI = "./api/registrations";
        const registration = {
            "guardianID": guardian.guardian_id, // get after creating the guardian
            "childID": child.childID, // get after creating the child
            "schoolID": school_id,
            "registrationFormID": registration_form_id,
            "status": "SUBMITTED"
        };
        const data = await post(URI, registration);
        return data.registrationID;
    } else {
        alert('Something went wrong when saving your data!');
        throw new Error('Something went wrong when saving data!');
    }
}

/**
 * Creates address, then guardian with that address and child.
 */
async function createGuardianAndChild() {
    if (!hasSession()) {
        let address_id = undefined;
        if (!address["addressID"]) {
            address_id = await createAddress();
        } else {
            address_id = address["addressID"];
        }
        if (!guardian["guardian_id"]) {
            await createGuardian(address_id);
        }
    }

    if (address.addressID && guardian.guardian_id) {
        if (!child["childID"]) {
            await createChild(); //check if hasChosenChild()
        }
    } else {
        alert('Saving address or guardian data failed!');
        throw new Error('Saving address or guardian data failed!');
    }

}

/**
 * Creates the Address object.
 * @returns {string} addressID for the creation of the Guardian
 */
async function createAddress() {
    const URI = "./api/addresses";
    const options = {
        method: 'POST',
        headers: {}
    };

    if (address !== undefined && address !== null) {
        options.headers['Content-Type'] = 'application/json';
        options.body = JSON.stringify(address);
    }

    try {
        const response = await fetch(URI, options);
        if (response.status === 500) {
            const error = await response.json();
            alert('An invalid input was detected! Please review your data inputs!');
            throw new Error(error.message);
        } else if (!response.ok && response.status !== 204 ) {
            const error = await response.json();
            throw new Error(error.message);
        }
        
        const data = await response.json();    
        address["addressID"] = data.addressID;
        return data.addressID;
        
    } catch (err) {
        BEDataFields = [];
        alert('Something went wrong!');
        throw err;
    }
}

/**
 * Creates the guardian after filling out the Guardian Details form.
 * @param {string} address_id
 */
async function createGuardian(address_id) {
    guardian["address_id"] = address_id;
    const URI = "./api/parents";

    const options = {
        method: 'POST',
        headers: {}
    };

    if (guardian !== undefined && guardian !== null && address_id !== undefined && address_id !== null) {
        options.headers['Content-Type'] = 'application/json';
        options.body = JSON.stringify(guardian);
    }

    try {
        const response = await fetch(URI, options);
        if (response.status === 500) {
            const error = await response.json();
            alert('An invalid input was detected! Please review your data inputs!');
            throw new Error(error.message);
        } else if (!response.ok && response.status !== 204 ) {
            const error = await response.json();
            throw new Error(error.message);
        }
        
        const data = await response.json();    
        guardian["guardian_id"] = data.guardian_id;
        
    } catch (err) {
        BEDataFields = [];
        alert('Something went wrong!');
        throw err;
    }
}

/**
 * Creates the child after filling out the Child Details form.
 */
async function createChild() {
    const URI = "./api/children";
    child["guardianId"] = guardian["guardian_id"];

    const options = {
        method: 'POST',
        headers: {}
    };

    if (guardian !== undefined && guardian !== null && guardian["guardian_id"]) {
        options.headers['Content-Type'] = 'application/json';
        options.body = JSON.stringify(child);
    }

    try {
        const response = await fetch(URI, options);
        if (response.status === 500) {
            const error = await response.json();
            alert('An invalid input was detected! Please review your data inputs!');
            throw new Error(error.message);
        } else if (!response.ok && response.status !== 204 ) {
            const error = await response.json();
            throw new Error(error.message);
        }
        
        const data = await response.json();    
        child["childID"] = data.childID;
        
    } catch (err) {
        BEDataFields = [];
        alert('Something went wrong!');
        throw err;
    }
}

/**
 * Loads the final page of the application process on which the Guardian Code/ID is displayed.
 */
function loadGuardianID() {
    if (!hasSession()) {
        const registrationFormElement = document.getElementById("registration-form");
        registrationFormElement.innerText = "";
        const registrationFormTitle = document.createElement("h1");
        registrationFormTitle.innerText = "Your Guardian Code";
        const gCode = document.createElement("h1");
        gCode.innerText = guardian.guardian_id;
        const info = document.createElement('p');
        info.setAttribute("id", "info");
        info.innerText = "Please, save this Guardian Code for future use.\nYou will only see it once - it will disappear after you close this page.";

        registrationFormElement.appendChild(registrationFormTitle);
        registrationFormElement.appendChild(gCode);
        registrationFormElement.appendChild(info);
    } else {
        alert('Successfully applied!');
        window.location.href = "/Topicus/schools.html";
    }
}

// ----- Account Management -----
/**
 * Retrieves data about all children related to this parent.
 * @returns {object|undefined} of all children related to this parent
 */
async function getChildrenByGuardian() {
    if (hasSession()) {
        const guardian_id = getSessionGuardianID();
        guardian["guardian_id"] = guardian_id;
        const URI = `./api/parents/${guardian_id}/children`;
        const children = await get(URI);
        if (children === undefined || children === null || children === '') {
            return undefined;
        }
        return children;
    } else {
        return undefined;
    }
}

/**
 * Sends a GET request for a child with that childID.
 * @param {string} childID 
 * @returns {object} the child object
 */
async function getChildByID(childID) {
    const URI = `./api/children/${childID}`;
    const childData = await get(URI);
    return childData;
}