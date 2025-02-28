// TODO: Implement the drop-down button with the function at the bottom of the document.
// TODO: Implement functionality for the search.
// TODO: sadmin should get school_id on log-in!

import {RegistrationView} from "./parentDashboard.js";
import {generateDropdownButtons} from "./administratorUtils.js";
import {getSessionSchoolID, getSessionUserID} from "./storageManagement.js";

// NECESSARY SESSION VARIABLES -------------------------------------------------------------------
const admin_id = getSessionUserID();
const sa_school_id = getSessionSchoolID();
const sa_regViews = [];
let displayed_views = [];
let status = "ALL";

sessionStorage.setItem("Admin", "true");
// INITIALIZATION ----------------------------------------------------------------------------------

/**
 * EventListener constructed to populate page with appropriate data.
 */
window.addEventListener("load", queryRegistrationsFromAdmin);

/**
 * Method used to clear the components of a DIV.
 * @param div
 */
function clearDiv(div) {
    div.innerHTML = "";
}

/**
 * Method to initialize the dashboard upon loading.
 */
function initializeDashboard() {
    sa_regViews.length = 0;
}

// POPULATION --------------------------------------------------------------------------------------

/**
 * The method that queries the database and populates the dashboard as a result.
 * @returns {Promise<void>}
 */
async function queryRegistrationsFromAdmin() {
    const container = document.getElementById("content");
    clearDiv(container);
    initializeDashboard();
    try {
        const URI = './api/schools/' + sa_school_id + '/registrationViews';
        const response = await fetch(URI);
        if (!response.ok) {
            throw new Error("Registration Details Unavailable At This Time");
        }
        const regViewList = await response.json();
        regViewList.map(regView => new RegistrationView(regView.status,
            regView.registration_id,
            regView.school_id,
            regView.guardian_name,
            regView.child_name,
            regView.guardian_id,
            regView.child_id,
            regView.school_name,
            regView.formTitle,
            regView.formYear)).forEach(reg => sa_regViews.push(reg));
        sa_regViews.forEach(view => {
            displayed_views.push(view);
        });
        const dropdown = generateDropdownButtons(sa_regViews);
        const sortSpace = document.getElementById("sortSpace");
        sortSpace.appendChild(dropdown);
        // container.innerHTML += initializeDescriptionColumn();
        for (const reg of displayed_views) {
            createListComponent(reg, container);
        }
        initializeDropdownButtons(container);
        console.log(JSON.stringify(regViewList));
    } catch (error) {
        console.log("An error has been produced.");
        alert("Something went wrong, please try again later.");
    }
}

// DASHBOARD CREATION ------------------------------------------------------------------------------

/**
 * This functionality filters the registration space.
 */
function initializeDropdownButtons(viewList) {
    const buttons = [];
    const div = document.getElementById("dropdown-buttons-container");
    buttons.push(document.getElementById("dropdown_button"), document.getElementById("dropDownForForms"), document.getElementById("dropDownForYear"));
    for (const button of buttons) {
        button.addEventListener("change", () => {
            displayByStatus(viewList);
        });
        div.appendChild(button);
    }
}

/**
 * This method is used to navigate to the view as an admin, which involves selecting the status.
 * @param registration_id
 */
function navigateToView(registration_id) {
    const rV = sa_regViews.find(view => {
        return view.registration_id === registration_id;
    });
    sessionStorage.setItem("selectedRegistration", JSON.stringify(rV));
    window.location.href = "/Topicus/viewRegistrationSchAdmin.html";
}

/**
 * Method to create the component in the list to be viewed on the dashboard.
 * @param regObject of type
 * @param container
 * @returns {string} of type String, representing HTML element.
 */
function createListComponent(regObject, container) {
    /**@type {RegistrationView} */
    const registrationView = regObject;
    const divToFill = document.createElement("div");
    divToFill.id = registrationView.registration_id + "";
    let result =
        '<div class="form-box">' +
        '<div class="context-box">' +
        '<div class="section">' +
        '<label class="section-name">Registration ID:</label>' +
        '<span class="registration_id">' + registrationView.registration_id + '</span>' +
        '</div>' +
        '<div class="section">' +
        '<label class="section-name">Child ID:</label>' +
        '<span class="child_id">' + registrationView.child_id + '</span>' +
        '</div>' +
        '<div class="section">' +
        '<label class="section-name">Child Name:</label>' +
        '<span class="child_name">' + registrationView.child_name + '</span>' +
        '</div>' +
        '<div class="section">' +
        '<label class="section-name">Guardian Name:</label>' +
        '<span class="guardian_name">' + registrationView.guardian_name + '</span>' +
        '</div>' +
        '<div class="section">' +
        '<label class="section-name">Registration Status:</label>' +
        '<span class="reg_status">' + registrationView.status + '</span>' +
        '</div>' +
        '<button id="view-form-1"' + registrationView.registration_id + '>View Form</button>' +
        '</div>' +
        '</div>';
    divToFill.innerHTML = result;
    container.appendChild(divToFill);
    document.getElementById("" + registrationView.registration_id)
        .addEventListener("click", function() {
            navigateToView(registrationView.registration_id);
        });
}

function addViewFunctionality(regObject, button) {

}

/**
 * This method is used to filter the elements of the dashboard by the status in which they appear.
 * @param container
 */
function displayByStatus(container) {
    console.log("Inside display-by-status");
    const selStatus = document.getElementById("dropdown_button").value;
    const selName = document.getElementById("dropDownForForms").value;
    const selYear = document.getElementById("dropDownForYear").value;
    // Repopulate the Page:
    clearDiv(container);
    // container.innerHTML += initializeDescriptionColumn();
    displayed_views.length = 0;
    sa_regViews.forEach(view => displayed_views.push(view));
    // If the statuses are all None, display everything, so true.
    if (selStatus === "NONE" && selName === "NONE" && selYear === "NONE") {} else {
        const filteredViews = [];
        if (selStatus !== "NONE") {
            displayed_views.forEach(view => {
                if (view.status === selStatus) {
                    filteredViews.push(view);
                }
            });
            filterRegistrationsNameYear(selName, selYear, filteredViews);
        } else {
            filterRegistrationsNameYear(selName, selYear, displayed_views);
        }
    }
    populateListView(displayed_views, container);
}

/**
 * This method is used for the filtering of registrations by name and year.
 * @param selName
 * @param selYear
 * @param filteredViews
 */
function filterRegistrationsNameYear(selName, selYear, filteredViews) {
    let nameValid = [];
    if (selName !== "NONE") {
        const val = filteredViews.filter(view => {
            return view.formTitle === selName;
        });
        val.forEach(valid => {
            nameValid.push(valid);
        })
    } else {
        nameValid = filteredViews;
    }
    let allValid = [];
    if (selYear !== "NONE") {
        const val = nameValid.filter(view => {
            return view.formYear + "" === selYear;
        });
        val.forEach(valid => {
            allValid.push(valid);
        });
    } else {
        allValid = nameValid;
    }
    displayed_views = allValid;
}

/**
 * This method is for populating the view of the registrations.
 * @param list
 * @param container
 */
function populateListView(list, container) {
    for (const reg of list) {
        createListComponent(reg, container);
    }
}

/**
 * This method is used to introduce the column of descriptions.
 */
