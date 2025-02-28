// EXPORTS ------------------------------------------------------------------------------------------------------------
import {invalidEditingStatus} from "./manageRegistration.js";
import {clearDiv} from "./formUtils.js";
import {getSessionGuardianID} from "./storageManagement.js";

/**
 * Class for managing the state of the page.
 */
export class PageStatus {
    static ViewOnly = new PageStatus("ViewOnly");
    static Editable = new PageStatus("Editable");
    static Basic = new PageStatus("Basic");

    constructor(name) {
        this.name = name;
    }

    returnName() {
        return this.name;
    }
}

// IMPORTS -----------------------------------------------------------------------------------------------------------
const guardian_id = getSessionGuardianID();

// DATA ---------------------------------------------------------------------------------------------------------------
/**
 * Class required for parsing RegistrationView from back-end.
 */
export class RegistrationView {
    constructor(status, registration_id, school_id, guardian_name, child_name, guardian_id, child_id, school_name, formTitle, formYear) {
        this.status = status;
        this.registration_id = registration_id;
        this.school_id = school_id;
        this.guardian_name = guardian_name;
        this.child_name = child_name;
        this.guardian_id = guardian_id;
        this.child_id = child_id;
        this.school_name = school_name;
        this.formTitle = formTitle;
        this.formYear = formYear;
    }
}

const regViews = [];

// METHODS ------------------------------------------------------------------------------------------------------------

/**
 * EventListener constructed so that the page is populated with the RegistrationViews immediately.
 */
window.addEventListener("load", async function() {
    if (window.location.pathname.includes("/Topicus/dashboard.html")) {
        await queryRegistrations();
    }
});

function changePages() {
    window.location.href = "/Topicus/viewRegistrationParent.html";
}

/**
 * Method to initialize the dashboard upon loading.
 */
function initializeDashboard() {
    regViews.length = 0;
}

/**
 * Method will produce the query results and populate the necessary variables with the required information.
 * @returns {Promise<void>}
 */
async function queryRegistrations() {
    console.log("Started Query");
    const ul = document.getElementById('registrations-list');
    clearDiv(ul);
    initializeDashboard();
    try {
        const URI = './api/registrations/registrationViews/' + guardian_id;
        const response = await fetch(URI);
        if (!response.ok) {
            throw new Error("Registration Details Unavailable At This Time!");
        }
        const regViewList = await response.json();
        console.log(JSON.stringify(regViewList));
        regViewList.map(regView => new RegistrationView(regView.status,
            regView.registration_id,
            regView.school_id,
            regView.guardian_name,
            regView.child_name,
            regView.guardian_id,
            regView.child_id,
            regView.school_name,
            regView.formTitle,
            regView.formYear)).forEach(reg => regViews.push(reg));
        console.log(JSON.stringify(regViews));
        for (const reg of regViews) {
            console.log(JSON.stringify(reg));
            /** @type {RegistrationView} */
            const regObj = reg;
            const docElem = document.createElement('li');
            docElem.classList.add("registrations");
            docElem.id = regObj.registration_id + "";
            docElem.innerHTML = createCard(regObj);
            console.log(docElem.innerHTML);
            ul.appendChild(docElem);
            // Creating IDs for buttons:
            let viewID = "v" + regObj.registration_id;
            console.log(viewID);
            let editID = "e" + regObj.registration_id;
            console.log(editID);
            // Collecting buttons:
            const vButton = document.getElementById(viewID + "");
            const eButton = document.getElementById(editID + "");
            console.log("After accessing");
            console.log(vButton.id);
            console.log(eButton.id);
            vButton.addEventListener("click", function() {
                initializeView("" + regObj.registration_id)
            });
            eButton.addEventListener("click", function() {
                initializeEdit("" + regObj.registration_id)
            });
            console.log("After eventListener");
        }
    } catch (error) {
        console.log("An error has been produced with message");
        alert("Something went wrong, please try again later.")
    }
}

// BUTTON GENERATION --------------------------------------------------------------------------------------------------
/**
 * The button that is clicked, whose parent node ID is used to set the appropriate page status.
 * @param registration_id
 */
function initializeView(registration_id) {
    console.log(registration_id);
    const rV = regViews.find(view => {
        return view.registration_id === registration_id;
    });
    sessionStorage.setItem("selectedRegistration", JSON.stringify(rV));
    sessionStorage.setItem("pageStatus", PageStatus.ViewOnly.returnName());
    changePages();
}

/**
 * The button that is clicked, whose parent node ID is used to set the appropriate page status.
 * @param registration_id
 */
function initializeEdit(registration_id) {
    const rV = regViews.find(view => {
        return view.registration_id === registration_id;
    });
    sessionStorage.setItem("selectedRegistration", JSON.stringify(rV));
    if (!invalidEditingStatus.includes(rV.status)) {
        sessionStorage.setItem("pageStatus", PageStatus.Editable.returnName());
    } else {
        sessionStorage.setItem("pageStatus", PageStatus.ViewOnly.returnName());
    }
    changePages();
}

/**
 * This method is used to add the buttons that will help navigate the front-end.
 * @param regObject of type Registration.
 * @returns {string}
 */
function createCard(regObject) {
    let viewID = "v" + regObject.registration_id;
    let editID = "e" + regObject.registration_id;
    return `<p class="img"><img src="assets/prob-school.jpg"></p>
            <p class="status submitted"><span class="status-text">${regObject.status}</span></p>
            <p>${regObject.child_name}</p>
            <p>${regObject.school_name}</p>
            <div class="button_container">
                 <button class="button" id="${viewID}">View</button>
                 <button class="button" id="${editID}">Edit</button>
            </div>`;
}