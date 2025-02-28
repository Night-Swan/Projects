import {applyStyles} from "./formUtils.js";
import {copyLink} from "./link-utils.js";

const urlParams = new URLSearchParams(window.location.search);
const schoolParam = urlParams.get('school_id');
const registrationFormParam = urlParams.get('form_id');
const selectedSchool = { "school_id": schoolParam };
const selectedRegistrationForm = { "form_id": registrationFormParam };

/**
 *  RegistrationForm class
 */
class RegistrationForm {
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

/**
 * FormComponent class
 */
class FormComponent {
    constructor(form_component_id, registration_form_id, section_id, position, title) {
        this.form_component_id = form_component_id;
        this.registration_form_id = registration_form_id;
        this.section_id = section_id;
        this.position = position;
        this.title = title;
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
 * Load the Registration Form when the page loads
 */
window.addEventListener("load", queryForm(selectedSchool["school_id"], selectedRegistrationForm["form_id"]));

/**
 * Method for parsing the registration form
 * @param registrationForm the registration form
 * @returns {RegistrationForm} the parsed registration form
 */
function parseRegistrationForm(registrationForm) {
    const registrationFormKeys = Object.keys(registrationForm);
    return new RegistrationForm(registrationForm[registrationFormKeys.at(0)], registrationForm[registrationFormKeys.at(1)], registrationForm[registrationFormKeys.at(2)], registrationForm[registrationFormKeys.at(3)], registrationForm[registrationFormKeys.at(4)], registrationForm[registrationFormKeys.at(5)], registrationForm[registrationFormKeys.at(6)], registrationForm[registrationFormKeys.at(7)], registrationForm[registrationFormKeys.at(8)]);
}

/**
 * Method for parsing a form component
 * @param formComponent the form component
 * @returns {FormComponent} the parsed form component
 */
function parseFormComponent(formComponent) {
    const formComponentKeys = Object.keys(formComponent);
    return new FormComponent(formComponent[formComponentKeys.at(0)], formComponent[formComponentKeys.at(1)], formComponent[formComponentKeys.at(2)], formComponent[formComponentKeys.at(3)], formComponent[formComponentKeys.at(4)]);
}

/**
 * Method for parsing the form components
 * @param formComponents the form components
 * @returns {Array} the parsed form components
 */
function parseFormComponents(formComponents) {
    const parsedFormComponents = [];
    for (let i = 0; i < formComponents.length; i++) {
        const formComponent = formComponents[i];
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
    for (let i = 0; i < sectionContainers.length; i++) {
        const sectionContainer = sectionContainers[i];
        const section = parseSection(sectionContainer["section"]);
        const formComponents = parseFormComponents(sectionContainer["formComponentList"]);
        parsedSectionContainers.push(new SectionContainer(section, formComponents));
    }
    return parsedSectionContainers;
}

/**
 * Query the database for the registration form
 */
function queryForm(school_id, registration_form_id) {
    let URI = "/Topicus/api/schools/";
    URI += school_id + "/forms/" + registration_form_id;
    fetch(URI).then(response => response.json()).then(registrationFormContainer => {
        if (registrationFormContainer !== null && registrationFormContainer !== undefined) {
            if (registrationFormContainer["formMetadata"] !== null && registrationFormContainer["formMetadata"] !== undefined) {
                console.log(registrationFormContainer);
                const registrationForm = parseRegistrationForm(registrationFormContainer["formMetadata"]);
                const sectionContainers = parseSectionContainers(registrationFormContainer["sectionContainerList"]);
                populateRegistrationForm(registrationForm, sectionContainers);
                const style = registrationFormContainer["formStyle"];
                console.log(JSON.stringify(style));
                applyStyles(style, "registration-form-field-set", "form-component-input", "section_headers");
                document.getElementById("registration-form").dataset.form_id = registrationForm.registration_form_id;
            }
        }
        else {
            console.log("ouch");
        }
    });
}

/**
 * Populate the registration form
 * @param registrationForm the registration form
 * @param sectionContainers the section containers
 */
function populateRegistrationForm(registrationForm, sectionContainers) {
    createFormElement();
    populateRegistrationFormDetails(registrationForm);
    populateSections(sectionContainers);
    populateFooterButtons();
}

/**
 * Create the form element
 * @returns {HTMLFormElement} the form element
 */
function createFormElement() {
    const formFieldSet = document.getElementById("registration-form-field-set");
    const formElement = document.createElement("form");
    formElement.setAttribute("id", "registration-form");
    formElement.setAttribute("action", "#");
    formElement.setAttribute("method", "post");
    formFieldSet.innerHTML = "";
    formFieldSet.appendChild(formElement);
}

/**
 * Populate the registration form details
 * @param registrationForm the registration form
 */
function populateRegistrationFormDetails(registrationForm) {
    const registrationFormElement = document.getElementById("registration-form");
    registrationFormElement.appendChild(createRegistrationFormDetails(registrationForm));
}

/**
 * Create the registration form details
 * @param registrationForm the registration form
 * @returns {HTMLDivElement} the registration form details
 */
function createRegistrationFormDetails(registrationForm) {
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
    registrationFormField.innerHTML = fieldValue;
    return registrationFormField;
}

/**
 * Populate the sections
 * @param sectionContainers the section containers
 */
function populateSections(sectionContainers) {
    const registrationFormElement = document.getElementById("registration-form");
    registrationFormElement.appendChild(createSections(sectionContainers));
}

/**
 * Create the sections
 * @param sectionContainers the section containers
 * @returns {HTMLDivElement} the sections
 */
function createSections(sectionContainers) {
    const sections = document.createElement("div");
    sections.setAttribute("id", "sections");
    sections.innerHTML = "";
    const orderedSectionContainers = sectionContainers.sort((a, b) => a.section.position - b.section.position);
    for (let i = 0; i < orderedSectionContainers.length; i++) {
        const sectionContainer = orderedSectionContainers[i];
        sections.appendChild(createSection(sectionContainer));
    }
    return sections;
}

/**
 * Create a section
 * @param sectionContainer the section container
 * @returns {HTMLDivElement} the section
 */
function createSection(sectionContainer) {
    const section = document.createElement("div");
    section.setAttribute("id", "section-" + sectionContainer.section.position);
    section.setAttribute("class", "section");
    section.appendChild(createSectionTitle(sectionContainer.section));
    section.appendChild(createSectionFormComponents(sectionContainer.formComponents));
    return section;
}

/**
 * Create the section title
 * @param section the section
 * @returns {HTMLParagraphElement} the section title
 */ 
function createSectionTitle(section) {
    const sectionDetails = document.createElement("p");
    sectionDetails.setAttribute("class", "section_headers");
    sectionDetails.innerHTML = section.title;
    return sectionDetails;
}


/**
 * Create the section form components
 * @param formComponents the form components
 * @returns {HTMLDivElement} the section form components
 */
function createSectionFormComponents(formComponents) {
    const sectionFormComponents = document.createElement("div");
    sectionFormComponents.setAttribute("class", "section-form-components");
    const orderedFormComponents = formComponents.sort((a, b) => a.position - b.position);
    for (let i = 0; i < orderedFormComponents.length; i++) {
        const formComponent = orderedFormComponents[i];
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
 * Create the form component label
 * @param formComponent the form component
 * @returns {HTMLLabelElement} the form component label
 */
function createFormComponentLabel(formComponent) {
    const formComponentLabel = document.createElement("label");
    formComponentLabel.setAttribute("class", "form-component-label");
    formComponentLabel.setAttribute("for", formComponent.title);
    formComponentLabel.innerHTML = formComponent.title;
    return formComponentLabel;
}

/**
 * Create the form component input
 * @param formComponent the form component
 * @returns {HTMLInputElement} the form component input
 */
function createFormComponentInput(formComponent) {
    const formComponentInput = document.createElement("input");
    formComponentInput.setAttribute("class", "form-component-input");
    formComponentInput.setAttribute("type", "text");
    formComponentInput.setAttribute("name", formComponent.title);
    formComponentInput.setAttribute("value", "");
    return formComponentInput;
}

/**
 * Populate the footer buttons
 */
function populateFooterButtons() {
    const registrationFormElement = document.getElementById("registration-form");
    registrationFormElement.appendChild(createFooterButtons());
    registrationFormElement.appendChild(generateShareLink());
}

/**
 * This method is used to generate the share link for the form.
 */
function generateShareLink() {
    // Get Link:
    let link = window.location.href;
    // Update Link:
    link = link.replace("viewFormSchoolAdmin", "applyForRegistration");
    // Create Share Section:
    const shareElem = document.createElement("p");
    shareElem.setAttribute("id", "share-paragraph");
    shareElem.innerText = `The link to share the form:`;
    shareElem.appendChild(document.createElement("br"));
    // Create Link Paragraph Element:
    const linkContainer = document.createElement("p");
    linkContainer.setAttribute("id", "get-form-link");
    linkContainer.innerText = link;
    shareElem.appendChild(linkContainer);
    // Create Link Button for Copying.
    const button = document.createElement("button");
    button.innerText = "Copy Link!";
    button.setAttribute("id", "copy-button");
    button.addEventListener("click", () => {
        copyLink("get-form-link");
    });
    shareElem.appendChild(button);
    return shareElem;
}

/**
 * Create footer buttons
 * @returns {HTMLDivElement} the footer buttons
 */
function createFooterButtons() {
    const footerButtons = document.createElement("div");
    footerButtons.setAttribute("id", "footer-buttons");
    const backButton = document.createElement("a");
    backButton.setAttribute("href", "/Topicus/viewSchoolForms.html");
    const backButtonInnerParagraph = document.createElement("p");
    backButtonInnerParagraph.setAttribute("class", "button");
    backButtonInnerParagraph.innerHTML = "Back";
    backButton.appendChild(backButtonInnerParagraph);
    footerButtons.appendChild(backButton);

    const editButton = document.createElement("a");
    editButton.setAttribute("href", "/Topicus/registrationadmin.html");
    const editButtonInnerParagraph = document.createElement("p");
    editButtonInnerParagraph.setAttribute("class", "button");
    editButtonInnerParagraph.innerHTML = "Edit";
    editButton.appendChild(editButtonInnerParagraph);
    footerButtons.appendChild(editButton);

    return footerButtons;
}
