// CLASSES ------------------------------------------------------------------------------------------------------------

import {addComponentButtons, addSectionButtons, initializeEssentials, scl_list} from "./registrationFormBuilder.js";
import {inputSanitizer} from "../fe_security/inputsanitizer.js";


const defaultStyles = {
    "background_color": "#eee7e7",
    "section_font_color": "#F8F9E5",
    "form_component_font_color": "#eee"
}

const allowedImageFormat = ["png", "jpeg"];
const allowedFileFormat = ["pdf", "doc", "docx"];

const DataTypeContainer = {
    "Text": "Text Field",
    "Date": "YYYY-MM-DD",
    "File": "File Upload",
    "Image": "Image Upload",
    "Number": "Number Field"
}

/**
 * This is the class used to send the creation of the registration form to the back-end, later to which the sections
 * and components will be added.
 * It is assumed that is_deleted is false upon the creation of the form.
 */
export class FERegistrationForm {
    constructor(school_id, title, description, year, education_type, is_active, start_date, is_deleted) {
        this.description = description;
        this.education_type = education_type;
        this.is_active = is_active;
        this.is_deleted = is_deleted;
        this.school_id = school_id;
        this.title = title;
        this.year = year;
        this.start_date = start_date;
    }
}

/**
 * This class is used to send the sections to the back-end for creation purposes.
 * NOTE: the registration_form_id comes from executing the fetch that creates the form first.
 * All Section names MUST be unique!
 */
export class FESection {
    constructor(registration_form_id, position_number, title) {
        this.registration_form_id = registration_form_id;
        this.position_number = position_number;
        this.title = title;
    }
}

/**
 * This class is used to send the components to the back-end for creation purposes.
 * Note: this class requires that the sections and components, before being sent, are stored in a list which are then
 * back-mapped to collect the relevant section_id.
 */
export class FEComponentSent {
    constructor(registration_form_id, section_id, position_number, title) {
        this.registration_form_id = registration_form_id;
        this.section_id = section_id;
        this.position_number = position_number;
        this.title = title;
    }
}

/**
 * This class is used to model the RegistrationForm.
 */
export class RegistrationFormDB {
    constructor(registration_form_meta_data, sections, style) {
        this.registration_form_meta_data = registration_form_meta_data;
        this.sections = sections;
        this.style = style;
    }
}

/**
 * This class is used to manage the style information for the back-end.
 */
export class Style {
    constructor(registration_form_id, section_font_color, form_component_font_color, background_color, logo) {
        this.registration_form_id = registration_form_id;
        this.section_font_color = section_font_color;
        this.form_component_font_color = form_component_font_color;
        this.background_color = background_color;
        this.logo = logo;
    }
}

/**
 * Method used to clear the components of a DIV.
 * @param div
 */
export function clearDiv(div) {
    div.innerHTML = "";
}
// UTILITY FUNCTIONS ---------------------------------------------------------------------------------------------------

/**
 * Method used to generate a description whenever possible.
 * @param description
 * @param className
 * @returns {HTMLParagraphElement}
 */
export function generateDescription(description, className) {
    const elem = document.createElement("p");
    elem.setAttribute("class", className);
    elem.innerHTML = "<h3>" + description + "</h3>";
    return elem;
}

/**
 * This method is used to sort a general list, based upon an attribute.
 * @param list
 * @param attribute
 */
export function sortList(list, attribute) {
    if (list !== null && list !== undefined && list.length !== 0) {
        return list.sort((e1, e2) => (e1[attribute] > e2[attribute]) ? 1 : (e1[attribute] < e2[attribute]) ? -1 : 0);
    }
}


// MANAGING ESSENTIALS -------------------------------------------------------------------------------------------------

/**
 * Method used to validate whether the date format is respected.
 * @param inputString
 * @returns {boolean}
 */
export function validateDateFormat(inputString) {
    let date_regex_concat = /^\d{4}-\d{2}-\d{2}$/;
    return date_regex_concat.test(inputString);
}

/**
 * Method used to validate whether the year format is respected.
 * @param inputString
 * @returns {boolean}
 */
export function validateYearFormat(inputString) {
    if (isNaN(parseInt(inputString))) {
        alert("You must provide a valid year.");
        return false;
    }
    return true;
}

/**
 * This method will take the file as the input, which will validate whether the file is valid according to size and type.
 * @param file representing the file.
 * @param type
 * @param size
 */
export function validateFileFormat(file, type, size) {
    let formats;
    switch (type) {
        case "FILE":
            formats = allowedFileFormat;
            break;
        case "IMAGE":
            formats = allowedImageFormat;
            break;
        default:
            alert("Internal Server Error");
            return;
    }
    if (file !== null && file !== undefined) {
        if (file.name !== null && file.name !== undefined && formats.includes((file.name).split(".").at(this.length - 1).toLowerCase())) {
            if (parseInt(file.size) <= parseInt(size)) {
                return true;
            }
        }
    }
    return false;
}

/**
 * Method used to test if a number is valid.
 * @param numberString
 * @returns {boolean}
 */
export function numberValidator(numberString) {
    return !isNaN(parseInt(numberString));
}

/**
 * This method is used to validate the format of the submission of a particular data field.
 * @param value
 * @param dataType
 * @param title
 */
export function validateDataField(value, dataType, title) {
    switch (dataType) {
        case "Number":
            if (!numberValidator(value)) {
                alert("Invalid Syntax for Field: " + title);
                return false;
            }
            break;
        case "Date":
            if (!validateDateFormat(value)) {
                alert("Invalid Syntax for Field: " + title);
                return false;
            }
            break;
        case "File":
            if (!validateFileFormat(value, dataType, 1000000)) {
                alert("File Invalid: Check size less than 1MB, and file type either PDF, DOC, DOCX.");
                return false;
            }
            break;
        case "Image":
            if (!validateFileFormat(value, dataType, 1000000)) {
                alert("Photo Invalid: Check size less than 1MB, and photo type either png or jpeg.");
                return false;
            }
            break;
        case "Text":
            if (!inputSanitizer(value)) {
                return false;
            }
            break;
    }
    return true;
}

/**
 * Method that assesses that the object contains the same fields as it is intended to.
 * @param fieldsList is the list of fields for the object.
 * @param obj represents an instance of the object being tested.
 * @returns {boolean}
 */
export function fieldValidator(fieldsList, obj) {
    let valid = true;
    if (fieldsList.length === Object.keys(obj).length) {
        fieldsList.forEach(field => {
            if (obj["" + field] !== null && obj["" + field] !== undefined) {
                valid = true;
            } else {
                valid = false;
            }
        });
    }
    return valid;
}

// CONSTANT HTML ELEMENTS ----------------------------------------------------------------------------------------------
/**
 * This method is used to return a static representation of the section row of the form builder.
 * @returns {string}
 */
export function sectionRow(section_id) {
    return `<div id='${section_id}' class='section-row'>
    <span id='sect-title-desc' class='attribute'>Section Title:</span>
    <input id='sect-title-input' class='input-field' type='text' maxlength='50' placeholder='Enter Title...'>
    <button id="add-component">Add Component</button>
    <button id="delete-section">Delete Section</button>
    <div id="components"></div>  
    </div>`;
}

/**
 * This method is used to return a static representation of the component row of the form builder.
 * @returns {string}
 */
export function compRow(comp_id) {
    return `<div id='${comp_id}' class='component-row'>
    <span id='comp-title-desc' class='attribute'>Component Title/Description:</span>
    <input id='comp-title-input' class='input-field' type='text' maxlength='50' placeholder='Enter Title/Description...'>
    <span id='type-select-desc' class='attribute'>Data Type:</span>
    <select id='data-type-select'>
        <option value='TEXT'>Text</option>
        <option value='NUMBER'>Number</option>
        <option value='FILE'>File</option>
        <option value='DATE'>Date</option>
    </select>
    <span id='mandatory-selector' class='attribute'>Mandatory?</span>
    <input id='mandatory-checkbox' class='input-field' type='checkbox'>
    <button id="delete-component">Delete Component</button>
    </div>`;
}

// STATUS --------------------------------------------------------------------------------------------------------------

/**
 * Class used for registrationFormBuilder.js to decide whether to display an existing form, or generate a new one.
 */
export class FormStatus {
    static Generate = new FormStatus("Generate");
    static Edit = new FormStatus("Editable");

    constructor(name) {
        this.name = name;
    }

    returnName() {
        return this.name;
    }
}

// POPULATE PAGE FUNCTIONS --------------------------------------------------------------------------------------------

/**
 * This method is used to build the form-field for a particular page, showing different input based on the fields described below.
 * @param title of the data field (expected String)
 * @param content of the data field (expected String)
 * @param mandatory shows whether a field is mandatory and should be validated as such (String: true, false)
 * @param dataType shows the data type (and hence, dictates the validation for the corresponding input) (string)
 * @param viewOnly shows whether the field should be view only (boolean)
 */
export function formFieldGenerator(title, content, mandatory, dataType, viewOnly) {
    const fieldSpan = document.createElement("span");
    fieldSpan.setAttribute("class", "field");
    fieldSpan.dataset.mandatory = mandatory;
    fieldSpan.appendChild(fieldLabelGenerator(title, mandatory, dataType));
    fieldSpan.appendChild(fieldInputGenerator(title, dataType, content, viewOnly, fieldSpan));
    return fieldSpan;
}

/**
 * This method is used to generate the label used for the information provision of the field.
 * @param title
 * @param mandatory
 * @param dataType
 * @returns {HTMLLabelElement} being the label.
 */
function fieldLabelGenerator(title, mandatory, dataType) {
    const arr = generateMandatoryDTStrings(mandatory, dataType);
    const infoLabel = document.createElement("label");
    infoLabel.setAttribute("class", "input-label-description");
    infoLabel.innerText = `${title}: \n[${arr[0]}, Input Style: ${arr[1]}]`;
    return infoLabel;
}

/**
 * Checks if the data type being passed is included in the
 * @param dataType
 * @returns Either returns the String of the Data Type, or it returns false (if not found).
 */
function checkIncludedDataType(dataType) {
    const keys = Object.keys(DataTypeContainer);
    console.log(dataType);
    for (const key of keys) {
        if (key.toLowerCase() === dataType.toLowerCase()) {
            console.log(key);
            return key;
        }
    }
    return false;
}

/**
 * This method is used to generate the input space for the field, depending on the data type.
 * @param title
 * @param dataType
 * @param content
 * @param viewOnly
 * @param fieldSpan
 */
function fieldInputGenerator(title, dataType, content, viewOnly, fieldSpan) {
    const input = document.createElement("input");
    input.setAttribute("class", "content-input");
    const dType = checkIncludedDataType(dataType);
    if (dType === false) {
        alert("There was a problem communicating with the server, please try again later, or contact an administrator.");
        return;
    }
    if (dType !== "File" && dType !== "Image") {
        if (viewOnly) {
            input.readOnly = true;
        }
    }
    input.dataset.componentTitle = title;
    switch (dType) {
        case "Text":
            applyType(input, dType, content);
            input.dataset.inputType = dType;
            break;
        case "Date":
            applyType(input, dType, content);
            input.dataset.inputType = dType;
            break;
        case "File":
            input.setAttribute("type", "file");
            input.dataset.inputType = dType;
            const labelOfFileName = document.createElement("label");
            labelOfFileName.setAttribute("class", "input-label-description");
            labelOfFileName.innerText = `You have submitted the file: ${content}`;
            fieldSpan.appendChild(labelOfFileName);
            break;
        case "Image":
            input.setAttribute("type", "file");
            input.dataset.inputType = dType;
            const imageLabel = document.createElement("label");
            imageLabel.setAttribute("class", "input-label-description");
            imageLabel.innerText = `You have submitted the image: ${content}`;
            fieldSpan.appendChild(imageLabel);
            break;
        case "Number":
            applyType(input, dType, content);
            input.dataset.inputType = dType;
            break;
    }
    return input;
}

/**
 * This method is used to apply the type for the element and assign the content as well.
 * @param element
 * @param type
 * @param content
 */
function applyType(element, type, content) {
    element.setAttribute("type", type);
    console.log("Element Content: " + content);
    element.setAttribute("value", content);
}

/**
 * This method is used to validate the mandatory and dataType fields.
 * @param mandatory
 * @param dataType
 * @returns {*[]}
 */
export function generateMandatoryDTStrings(mandatory, dataType) {
    const returnArray = [];
    let mString = generateMandatoryString(mandatory);
    let dType = generateDataTypeString(dataType);
    returnArray.push(mString);
    returnArray.push(dType);
    return returnArray;
}

/**
 * Returns the String for the front-end to display in case a field is mandatory.
 * @param mandatory
 * @returns {string}
 */
function generateMandatoryString(mandatory) {
    if (mandatory === "false") {
        return "Mandatory";
    } else {
        return "Optional";
    }
}

/**
 * Returns a String for the Front-End to Display regarding the Data Type.
 * @param dataType
 * @returns {string}
 */
function generateDataTypeString(dataType) {
    let dt = "NONE";
    Object.keys(DataTypeContainer).forEach(key => {
        if (key === dataType) {
            dt = DataTypeContainer[`${key}`];
            return dt;
        }
    });
    return dt;
}

/**
 * This method is used to populate the essentials for the page.
 * @param formMetaData
 */
export function populateEssentials(formMetaData) {
    const essentials = document.getElementsByClassName("essential-input-field");
    for (const essential of essentials) {
        switch (essential.id) {
            case "title":
                essential.value = formMetaData.title;
                break;
            case "description":
                essential.value = formMetaData.description;
                break;
            case "year":
                essential.value = formMetaData.year;
                break;
            case "education_type":
                essential.value = formMetaData.education_type;
                break;
            case "isActive":
                if (formMetaData.is_active === "true") {
                    essential.value = "Y";
                } else {
                    essential.value = "N";
                }
                break;
            case "startDate":
                const date = new Date(parseFloat(formMetaData.start_date));
                essential.value = formatDate(date);
                break;
        }
        console.log("Essential Value: " + essential.value);
    }
}

/**
 * This is a utility function to format the date correctly.
 * @param date
 * @returns {string}
 */
function formatDate(date) {
    const yString = date.getFullYear();
    const mString = String(date.getMonth() + 1).padStart(2, '0');
    const dString = String(date.getDate()).padStart(2, '0');
    return `${yString}-${mString}-${dString}`;
}

/**
 * This method is used to populate the sections of the Registration Form.
 * All sections from the form have the id and other properties that need to be assigned.
 * All sections have the appropriate ids and other properties that need to be assigned.
 * @param html_space
 * @param sectionContainerList
 */
export function populateBuilder(html_space, sectionContainerList) {
    const parser = new DOMParser();
    sectionContainerList.forEach(sectCont => {
        /**@type {SectionContainer} */
        const container = sectCont;
        console.log("Container: " + JSON.stringify(container));
        const sect = container.section;
        const comps = container.formComponentList;
        const section = parser.parseFromString(sectionRow(sect.section_id), 'text/html').body.firstChild;
        section.childNodes.forEach(node => {
            if (node.id === "sect-title-input") {
                node.value = sect.title;
            }
            addSectionButtons(node, section);
        });
        populateComponents(comps, section);
        html_space.appendChild(section);
    });
}

/**
 * This method is used to populate the details for all the components of a section.
 * @param components_list
 * @param node
 */
function populateComponents(components_list, node) {
    if (components_list !== null && components_list !== undefined && components_list.length !== 0) {
        components_list.forEach(component => {
            node.appendChild(populateComponent(component));
        });
    }
}

/**
 * This method is used to populate the details for a component.
 * @param component
 * @returns {ChildNode}
 */
function populateComponent(component) {
    const parser = new DOMParser();
    const comp = parser.parseFromString(compRow(component.component_id), 'text/html').body.firstChild;
    comp.childNodes.forEach(node => {
        addComponentButtons(node, component);
        switch (node.id) {
            case "comp-title-input":
                node.value = component.title;
                break;
            case "data-type-select":
                Array.from(node.options).forEach(option => {
                    if (option.value === component.data_type) {
                        node.value = component.data_type;
                    }
                });
                break;
            case "mandatory-checkbox":
                node.checked = component.mandatory !== false;
                break;
        }
    });
    return comp;
}

/**
 * This method is used to apply the styling for the form.
 * @param style
 */
export function populateStyler(style) {
   /**@type {Style} */
   const st = style;
   if (style !== null && style !== undefined) {
       document.getElementById("section-color-selector").value = st.section_font_color;
       document.getElementById("comp-color-selector").value = st.form_component_font_color;
       document.getElementById("background-color-selector").value = st.background_color;

   }
}

function applyLogo() {

}

/**
 * This method is used to add the styling to the page.
 * @param style
 * @param backgroundElem
 * @param contentElem
 * @param sectionElem
 */
export function applyStyles(style, backgroundElem, contentElem, sectionElem) {
    if (style !== null && style !== undefined) {
        applyBackColor(style.background_color, backgroundElem);
        applySectionColor(style.section_font_color, sectionElem);
        applyTextBoxColor(style.form_component_font_color, contentElem);
    } else {
        applyBackColor(defaultStyles.background_color, backgroundElem);
        applySectionColor(defaultStyles.section_font_color, sectionElem);
        applyTextBoxColor(defaultStyles.form_component_font_color, contentElem);
    }
}

/**
 * This method is used to add the styling to the background.
 * @param backColor
 * @param html
 */
function applyBackColor(backColor, html) {
    if (backColor !== null && backColor !== undefined && backColor !== "#000000") {
        document.getElementById(html).style.backgroundColor = backColor;
    } else {
        document.getElementById(html).backgroundColor = defaultStyles.background_color;
    }
}

/**
 * This method is used to add the styling to the Section Headers.
 * @param sectColor
 */
function applySectionColor(sectColor, html) {
    if (sectColor !== null && sectColor !== undefined) {
        for (let elem of document.getElementsByClassName(html)) {
            elem.style.backgroundColor = sectColor;
        }
    } else {
        for (let elem of document.getElementsByClassName(html)) {
            elem.style.backgroundColor = defaultStyles.section_font_color;
        }
    }
}

/**
 * This method is used to add the styling for the text boxes background.
 * @param textBoxColor
 * @param html
 */
function applyTextBoxColor(textBoxColor, html) {
    if (textBoxColor !== null && textBoxColor !== undefined && textBoxColor !== "#000000") {
        for (let elem of document.getElementsByClassName(html)) {
            elem.style.backgroundColor = textBoxColor;
        }
    } else {
        for (let elem of document.getElementsByClassName(html)) {
            elem.style.backgroundColor = defaultStyles.form_component_font_color;
        }
    }
}

/**
 * This method is used to perform the query for the styling.
 * @returns {Promise<void>}
 */
export async function queryStyles(reg_id, reg_form_id, background, input, section) {
    let URI = "/Topicus/api/registrations/" + reg_id + "/style?formID=" + reg_form_id;
    console.log(URI);
    try {
        const response = await fetch(URI);
        if (!response.ok) {
            throw new Error("Invalid Response from Server");
        }
        const style = await response.json();
        console.log(JSON.stringify(style));
        applyStyles(style, background, input, section);
    } catch (Error) {
        alert("Could not reach the database.");
    }
}
