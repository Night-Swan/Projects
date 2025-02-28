/**
 * This method is used to generate all the drop-down buttons.
 * @param reg_view_list
 */
export function generateDropdownButtons(reg_view_list) {
    const containerDiv = document.createElement("div");
    containerDiv.setAttribute("id", "dropdown_container");
    containerDiv.appendChild(generateDropDownForFilter());
    const names = [];
    reg_view_list.map(view => {
        if (!names.includes(view.formTitle)) {
            names.push(view.formTitle);
        }}
    );
    containerDiv.appendChild(document.createElement("br"));
    containerDiv.appendChild(generateDropDownForForms(names));
    const years = [];
    reg_view_list.map(view => {
        if (!years.includes(view.formYear)) {
            years.push(view.formYear);
        }
    });
    containerDiv.appendChild(document.createElement("br"));
    containerDiv.appendChild(generateDropDownForYear(years));
    return containerDiv;
}

/**
 * This method is used to create the drop-down button for the years.
 * @param years
 * @returns {HTMLSelectElement}
 */
export function generateDropDownForYear(years) {
    const dropdownButton = document.createElement("select");
    dropdownButton.setAttribute("id", "dropDownForYear");
    let result = "<option value='NONE' selected>NONE</option>";
    years.forEach(year => {
        if (!result.includes(year)) {
            result += optionBuilder(year);
        }
    });
    dropdownButton.innerHTML = result;
    return dropdownButton;
}

/**
 * Generates the HTML element for the drop-down buttons for the administrator to select from.
 * @returns {HTMLElement}
 */
export function generateDropDownForChangingStatus() {
    const dropdownButton = document.createElement("select");
    dropdownButton.setAttribute("id", "dropdown_button");
    dropdownButton.innerHTML =
        '<option value="ACCEPTED">ACCEPT</option> ' +
        '<option value="REJECTED">REJECT</option> ' +
        '<option value="UNDER_REVIEW">UNDER REVIEW</option> ' +
        '<option value="MODIFICATIONS_ALLOWED">ALLOW MODIFICATIONS</option>';
    return dropdownButton;
}

/**
 * This method is used to generate the drop-down button for the filter which filters registrations by the name of the form.
 * @param formNames
 * @returns {HTMLSelectElement}
 */
export function generateDropDownForForms(formNames) {
    const dropdownButton = document.createElement("select");
    dropdownButton.setAttribute("id", "dropDownForForms");
    let result = "<option value='NONE' selected>NONE</option>";
    formNames.forEach(name => {
        if (!result.includes(name)) {
            result += optionBuilder(name);
        }
    });
    dropdownButton.innerHTML = result;
    return dropdownButton;
}

/**
 * This method is used to produce the option string.
 * @param value
 * @returns {string}
 */
function optionBuilder(value) {
    return "<option value='" + value + "'>" + value + "</option>";
}

/**
 * Generate DropDown for Filter.
 * @returns {HTMLSelectElement}
 */
export function generateDropDownForFilter() {
    const dropdownButton = document.createElement("select");
    dropdownButton.setAttribute("id", "dropdown_button");
    dropdownButton.innerHTML =
        "<option value='NONE' selected>NONE</option>" +
        '<option value="ACCEPTED">ACCEPTED</option> ' +
        '<option value="REJECTED">REJECTED</option> ' +
        '<option value="UNDER_REVIEW">UNDER REVIEW</option> ' +
        '<option value="MODIFICATIONS_ALLOWED">MODIFICATIONS ALLOWED</option>' +
        '<option value="AWAITING_SUBMISSION">AWAITING SUBMISSION</option>' +
        '<option value="SUBMITTED">SUBMITTED</option>' +
        '<option value="MISSING_INFORMATION">MISSING INFORMATION</option>' +
        '<option value="UNAVAILABLE_ERROR">ERRORS</option>';
    return dropdownButton;
}
