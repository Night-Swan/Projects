// NECESSARY VARIABLES FROM SESSION -----------------------------------------------------------------------------------
import {
    FERegistrationForm,
    generateDescription,
    validateDateFormat,
    sectionRow,
    compRow,
    populateEssentials, populateBuilder, populateStyler,
    Style, numberValidator
} from "./formUtils.js";
import { renderPopup, showPopup, hidePopup } from "./popup.js";
import {getSessionSchoolID, getSessionUserID} from "./storageManagement.js";

const school_id = getSessionSchoolID();
const required_form_elements = ["Title:", "Description:", "Year:", "Education Type:", "Release On Submission (Will be Usable, Y for Yes, N for No):", "Start Date (in YYYY-MM-DD format):"];
const parser = new DOMParser();
let savedRegistrationForm = null;
export const scl_list = [];

// NECESSARY CLASS -----------------------------------------------------------------------------------------------------

/**
 * This class is used to send the creation of the Registration.
 */
export class RegistrationSubmission {
    constructor(formMetadata, sectionContainerList, style) {
        this.formMetadata = formMetadata;
        this.sectionContainerList = sectionContainerList;
        this.formStyle = style;
    }
}

/**
 * This class is used to produce the containers for the section and its respective list of components.
 */
export class SectionContainer {
    constructor(section, formComponentList) {
        this.section = section;
        this.formComponentList = formComponentList;
    }
}

let registrationSubmission = new RegistrationSubmission();


// INITIALIZE PAGE -----------------------------------------------------------------------------------------------------

/**
 * This method is used to initialize the entire page. The descriptions and builders are produced as required.
 * However, in the event that a form is being edited (an existing form), then the front-end dynamically adapts to presenting the data fields for that form as required.
 */
function initializePage() {
    if (window.location.pathname.includes("/Topicus/registrationadmin.html")) {
        const status = sessionStorage.getItem("formStatus");
        initializeEssentials();
        initializeBuilder();
        initializeStyles();
        switch(status) {
            case "Editable":
                /**@type {RegistrationSubmission} */
                const registrationForm = JSON.parse(sessionStorage.getItem("registrationFormDB"));
                console.log(JSON.stringify(registrationForm.formMetadata));
                populateEssentials(registrationForm.formMetadata);
                populateBuilder(document.getElementById("form-editor"), registrationForm.sectionContainerList);
                populateStyler(registrationForm.formStyle);
                break;
        }
        document.getElementById("save_button").addEventListener("click", async function() {
            await handleSubmission();
        });
    }
}

// INITIALIZING FUNCTIONS ----------------------------------------------------------------------------------------------
/**
 * This method is used to initialize the styles. It sets the default values for the styles in the sessionStorage, later to be changed.
 */
function initializeStyles() {
    sessionStorage.setItem("sectFontColor", "#000000");
    sessionStorage.setItem("compFontColor", "#000000");
    sessionStorage.setItem("backColor", "#000000");
}

/**
 * This method is used to produce the style information.
 * @param registration_form_id
 * @returns {Style}
 */
function produceStyle(registration_form_id) {
    const style = new Style();
    style.form_component_font_color = sessionStorage.getItem("compFontColor");
    style.section_font_color = sessionStorage.getItem("sectFontColor");
    style.background_color = sessionStorage.getItem("backColor");
    style.logo = sessionStorage.getItem("logo");
    if (registration_form_id !== undefined) {
        style.registration_form_id = registration_form_id;
    }
    return style;
}

/**
 * Initializes the page based on the previously defined function.
 */
window.onload = initializePage();

/**
 * This method is used to initialize the essentials of the page. Essentials are the form-meta-data that is required.
 */
export function initializeEssentials() {
    const essentialDescription = document.getElementById("form_essentials_description");
    const essentialForm = document.getElementById("form_essentials_input");
    const description = generateFormEssentialsDescription();
    const form = generateEssentialsForm();
    essentialDescription.appendChild(description);
    essentialForm.appendChild(form);
}

// ENTITY-MANAGEMENT FUNCTIONS --------------------------------------------------------------------------------------------------

/**
 * This method is used to create the row for the HTML section entity details.
 */
function addSectionRow() {
    const section = parser.parseFromString(sectionRow("NONE"), 'text/html').body.firstChild;
    section.childNodes.forEach(node => {
        addSectionButtons(node, section);
    });
    document.getElementById("form-editor").appendChild(section);
}

/**
 * This method is used to add the buttons to the section, for adding HTML components entities or deleting the HTML section entity.
 * @param node
 * @param section
 */
export function addSectionButtons(node, section) {
    if (node.id === "add-component") {
        node.addEventListener("click", () => {
            addComponent(section)
        });
    } else if (node.id === "delete-section") {
        node.addEventListener("click", () => {
            removeSection(section)
        });
    }
}

/**
 * This method is used to remove the HTML section entity.
 * @param section
 */
export function removeSection(section) {
    section.remove();
}

/**
 * This method is used to manage the addition of the HTML component entity to the HTML section entity it belongs to.
 * @param section
 */
function addComponent(section) {
    section.childNodes.forEach(node => {
        if (node.id === "components") {
            const component = parser.parseFromString(compRow("NONE"), 'text/html').body.firstChild;
            component.childNodes.forEach(node => {
                addComponentButtons(node, component);
            });
            node.appendChild(component);
        }
    });
}

/**
 * This method is used to add the button functionality for an HTML component entity.
 * @param node
 * @param component
 */
export function addComponentButtons(node, component) {
    if (node.id === "delete-component") {
        node.addEventListener("click", () => {
            removeComponent(component);
        })
    }
}

/**
 * This method is used to remove the HTML component entity.
 * @param component
 */
export function removeComponent(component) {
    component.remove();
}

// GENERATING ESSENTIALS FORM -------------------------------------------------------------------------------------------

/**
 * This method is used to generate the description of the essential elements of the form. (Meta-Data).
 * @returns {HTMLParagraphElement}
 */
function generateFormEssentialsDescription() {
    return generateDescription("Please fill out the meta-information for the form before submission.", "description_text");
}

/**
 * This method is used to generate the form that is used for creating the description of a form.
 */
function generateEssentialsForm() {
    const elem = document.createElement("div");
    elem.setAttribute("class", "page_form");
    elem.innerHTML = generateEssentialsInputFields();
    return elem;
}

/**
 * Method to return the input fields for the form.
 * @returns {string}
 */
function generateEssentialsInputFields() {
    return essentialsFieldBuilder(required_form_elements[0], "title", "fd_field", "50", "text", "essential-input-field") +
        essentialsFieldBuilder(required_form_elements[1], "description", "fd_field", "100", "text", "essential-input-field") +
        essentialsFieldBuilder(required_form_elements[2], "year", "fd_field", "4", "text", "essential-input-field") +
        essentialsFieldBuilder(required_form_elements[3], "education_type", "fd_field", "25", "text", "essential-input-field") +
        essentialsFieldBuilder(required_form_elements[4], "isActive", "fd_field", "1", "text", "essential-input-field") +
        essentialsFieldBuilder(required_form_elements[5], "startDate", "fd_field", "10", "text", "essential-input-field");
}

/**
 * This function builds the fields for the description of the form.
 * @param title
 * @param id
 * @param class_to_add
 * @param maxLength
 * @param type
 * @param classOfInput
 * @returns {string}
 */
function essentialsFieldBuilder(title, id, class_to_add, maxLength, type, classOfInput) {
    if (maxLength === "") {
        return "<span class='" + class_to_add + "'><label>" + title + "</label> <input class='" + classOfInput + "' id='" + id + "'type='" + type + "'></span><br>";
    } else {
        return "<span class='" + class_to_add + "'><label>" + title + "</label> <input class='" + classOfInput + "' id='" + id + "'type='" + type + "' maxlength='" + maxLength + "'></span><br>";
    }
}

// GENERATING FORM BUILDER ---------------------------------------------------------------------------------------------

/**
 * This method is used to create the form builder.
 */
function initializeBuilder() {
    const formBuilder = document.getElementById("addition-description");
    document.getElementById("add-section-button").addEventListener("click", addSectionRow);
    formBuilder.appendChild(initializeBuilderDescription());
}

/**
 * This function is used to generate the description for the form builder tool.
 * @returns {HTMLParagraphElement}
 */
function initializeBuilderDescription() {
    return generateDescription("Please use the button below to insert sections into the form, setting all the fields as required.", "description_text");
}

// DATA PROCESSING METHODS ---------------------------------------------------------------------------------------------

/**
 * This is used to send the section to the back-end.
 * A BE section can also have a registration_form_id, which is dynamically appended.
 */
export class SentSection {
    constructor(position_number, title) {
        this.position_number = position_number;
        this.title = title;
    }
}

/**
 * This class is used to send a component to the back-end. It can have section_id, registration_form_id, and component_id
 * depending on existence.
 */
export class SentComponent {
    constructor(position, title, mandatory, data_type) {
        this.position = position;
        this.title = title;
        this.mandatory = mandatory;
        this.data_type = data_type;
    }
}

/**
 * This method is used to parse all the data into the appropriate classes, ready for transportation.
 */
function prepareDataForTransport() {
    /**@type {RegistrationSubmission} */
    const registrationForm = JSON.parse(sessionStorage.getItem("registrationFormDB"));
    if (registrationForm !== undefined && registrationForm !== null) {
        return !!(processEssentials(registrationForm.formMetadata.registration_form_id) && prepareSectionsComponents());
    }
    return !!(processEssentials() && prepareSectionsComponents());
}

// PREPARING ESSENTIAL REGISTRATION FORM DATA --------------------------------------------------------------------------

/**
 * This method is used to collect the input from the form when the submit button is pressed.
 */
function processEssentials(registration_form_id) {
    const fd_fields = document.getElementsByClassName("essential-input-field");
    let reg = new FERegistrationForm();
    for (const field of fd_fields) {
        switch(field.id) {
            case "title":
                reg.title = field.value;
                break;
            case "description":
                reg.description = field.value;
                break;
            case "year":
                /**@type {String} */
                let yearString = field.value;
                if (numberValidator(yearString)) {
                    reg.year = field.value;
                } else {
                    return false;
                }
                break;
            case "education_type":
                reg.education_type = field.value;
                break;
            case "isActive":
                /**@type {String} */
                let value = field.value;
                switch(value.toLowerCase()) {
                    case "y":
                        reg.is_active = true;
                        break;
                    case "n":
                        reg.is_active = false;
                        break;
                    default:
                        return false;
                }
                break;
            case "startDate":
                /**@type {String} */
                let dateString = field.value;
                if (validateDateFormat(dateString)) {
                    reg.start_date = dateString;
                } else {
                    return false;
                }
                break;
            default:
                console.log("Invalid ID taken!");
                return;
        }
    }
    // If we are processing essentials of an EXISTING FORM:
    if (registration_form_id !== undefined) {
        reg.registration_form_id = registration_form_id;
    }
    reg.school_id = school_id;
    reg.is_deleted = false;
    savedRegistrationForm = reg;
    registrationSubmission.formMetadata = savedRegistrationForm;
    registrationSubmission.formStyle = produceStyle(registration_form_id);
    console.log(JSON.stringify(reg));
    return true;
}

// PREPARING SECTIONS AND COMPONENTS -----------------------------------------------------------------------------------

/**
 * This method is used to prepare the components and sections.
 * @returns {boolean}
 */
export function prepareSectionsComponents() {
    const sectionDivs = document.getElementsByClassName("section-row");
    scl_list.length = 0;
    for (const div of sectionDivs) {
        /**@type {SectionContainer} */
        let sect = parseSection(div);
        if (sect !== null) {
            scl_list.push(sect);
        } else {
            alert("Invalid entity: make sure no entities are empty, no duplicates either.");
            return false;
        }
    }
    registrationSubmission.sectionContainerList = scl_list;
    console.log("The final object being sent: " + JSON.stringify(registrationSubmission));
    return true;
}

/**
 * This method is used to parse a HTML section to a SectionContainer, in both cases where new sections or previous sections.
 * @param div
 * @returns {SectionContainer}
 */
function parseSection(div) {
    /**@type {SectionContainer} */
    let sectCont = new SectionContainer();

    // Getting the children from the Section HTML:
    const children = div.children;
    const section = new SentSection();

    // Initializing IDs (depending on Existence):
    if (div.id !== "NONE") {
        section.section_id = div.id;
        // Now Check if SavedRegistrationForm is defined and if has a registration_form_id (existing form):
    } else if (savedRegistrationForm !== undefined && savedRegistrationForm !== null) {
        if (savedRegistrationForm.registration_form_id !== undefined) {
            section.registration_form_id = savedRegistrationForm.registration_form_id;
        }
    }

    // Initializing HTML List of Components And Completing Section Parsing:
    let componentsDiv;
    for (const child of children) {
        if (child.id === "sect-title-input") {
            const title = child.value;
            if (title !== null && title !== "") {
                section.title = title;
            } else {
                return false;
            }
        } else if (child.id === "components") {
            componentsDiv = child;
        }
    }

    // As the position number varies depending on user changes, it is recalibrated:
    section.position_number = scl_list.length + 1;
    // Parsing Components (componentsDiv is the HTML Div that Contains the HTML CompRows):
    sectCont.formComponentList = parseComponents(componentsDiv, section.section_id, section.registration_form_id);
    if (section.title !== "") {
        sectCont.section = section;
        return sectCont;
    } else {
        return null;
    }
}

/**
 * This method is used to parse the components in their HTML state to classes.
 * @param listDiv
 * @param section_id
 * @param registration_form_id
 * @returns {*[]}
 */
function parseComponents(listDiv, section_id, registration_form_id) {
    const children = listDiv.children;
    const componentList = [];
    let pos = 1;
    for (const child of children) {
        const component = parseComponent(child, pos);
        if (component !== null) {
            // If part of a real section:
            if (section_id !== undefined && registration_form_id !== undefined) {
                component.section_id = section_id;
                component.registration_form_id = registration_form_id;
            }
            componentList.push(component);
        } else {
            return null;
        }
        pos++;
    }
    return componentList;
}

/**
 * This method is used to parse the component from HTML to class;
 * @param componentDiv
 * @param positionNumber
 * @returns {SentComponent}
 */
function parseComponent(componentDiv, positionNumber) {
    const component = new SentComponent();
    componentDiv.childNodes.forEach(node => {
        if (node.id === "comp-title-input") {
            component.title = node.value;
        } else if (node.id === "data-type-select") {
            component.data_type = node.value;
        } else if (node.id === "mandatory-checkbox") {
            component.mandatory = node.checked;
        }
    });
    component.position = positionNumber;
    if (component.title === "" || component.data_type === undefined) {
        return null;
    }
    return component;
}

// SUBMISSION ----------------------------------------------------------------------------------------------------------
/**
 * This method is used to perform the submission.
 * @returns {Promise<void>}
 */
async function handleSubmission() {
    prepareDataForTransport();
    await queryFormCreation();
}

// FETCH ---------------------------------------------------------------------------------------------------------------

/**
 * This method is used to send the request to create the basic form details record in the database.
 */
async function queryFormCreation() {
    const fe_rf = registrationSubmission;
    if (fe_rf !== null && fe_rf !== undefined) {
        let URI = "./api/schools/" + school_id + "/forms";
        try {
            const response = await fetch(URI, {
                headers: {
                    "Content-Type": "application/json"
                },
                method: "POST",
                body: JSON.stringify(fe_rf)
            });
            if (!response.ok) {
                throw new Error("The server could not be reached in time.");
            }
            const registration_form = await response.json();
            if (registration_form !== null && registration_form !== undefined) {
                savedRegistrationForm = registration_form;
            }
            alert("Your request was successful.")
            window.location.href = "/Topicus/viewSchoolForms.html";
        } catch (Error) {
            alert("Something went wrong.");
        }
    }
}