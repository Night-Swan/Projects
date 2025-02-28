// EXPORTS -------------------------------------------------------------------------------------------------------------

import { del } from "./requests.js";

/**
 * Class for managing the state of the page.
 */
class PageStatus {
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
//IMPORTS---------------------------------------------------------------------------------------------------------------

// DATA ----------------------------------------------------------------------------------------------------------------
/**
 * Class required for parsing SchoolView from back-end.
 */
class SchoolView {
    constructor(school_id, address_id, name, type, phone_number, email, postalCode, streetName, streetNumber, city, country, phoneNumber) {
        this.school_id = school_id;
        this.address_id = address_id;
        this.type = type;
        this.name = name;
        this.phone_number = phone_number;
        this.email = email;
        this.postalCode = postalCode;
        this.streetName = streetName;
        this.streetNumber = streetNumber;
        this.city = city;
        this.country = country;
        this.phoneNumber = phoneNumber;
        //this.image = image;
    }
}
/**
 * Class required for parsing AdministratorView from back-end.
 */
class AdministratorView {
    constructor(adminID, type, username, email, surname, phoneNumber, birthDate, givenNames, schoolID, employeeID) {
        this.adminID = adminID;
        this.type = type;
        this.username = username;
        this.email = email;
        this.surname = surname;
        this.phoneNumber = phoneNumber;
        this.birthDate = birthDate;
        this.givenNames = givenNames
        this.schoolID = schoolID;
        this.employeeID = employeeID;
    }
}
const admViews = [];
const schViews = [];
const allAdmins = [];
const mainDiv = document.getElementById("content");
// METHODS ------------------------------------------------------------------------------------------------------------
/**
 * Method to initialize the dashboard upon loading.
 */
function initializeDashboard() {
    schViews.length = 0;
}
/**
 * Method to empty admins before querying again for them
 */
function emptyAdmin() {
    admViews.length = 0;
}
/**
 * Method used to clear the components of a DIV.
 * @param div
 */
function clearDiv(div) {
    div.innerHTML = "";
}
/**
 * EventListener constructed so that the page is populated with the SchoolViews immediately.
 */
window.addEventListener("load", async function () {
    if (window.location.pathname.includes("topicusadmindashboard.html")) {
        await querySchools();
    }
});

function changePagesViewSchool() {
    window.location.href = "/Topicus/topicusViewSchool.html";
}
function changePagesViewAdmin() {
    window.location.href = "/Topicus/topicusviewschooladmin.html";
}
function changePagesAddSchool() {
    window.location.href = "/Topicus/topicusAddSchool.html";
}
function changePagesAddSchoolAdmin(school_id) {
    sessionStorage.setItem("schoolID", school_id);
    window.location.href = "/Topicus/topicusaddschooladmin.html";
}
async function getAllAdmins() {
    try {
        const URI = './api/users/school_admins';
        const response = await fetch(URI);
        if (!response.ok) {
            throw new Error("Admins Unavailable At This Time!");
        }
        const admList = await response.json();
        console.log(JSON.stringify(admList));
        admList.map(admView => new AdministratorView(
            admView.adminID,
            admView.type,
            admView.username,
            admView.email,
            admView.surname,
            admView.phoneNumber,
            admView.birthDate,
            admView.givenNames,
            admView.schoolID,
            admView.employeeID)).forEach(adm => allAdmins.push(adm));
        console.log("All admins(allAdmins): " + JSON.stringify(allAdmins));
    } catch (error) {
        console.log("An error has been produced with message");
        alert("Something went wrong, please try again later.")
    }
}
async function queryAdmins(school_id, schoolDiv) {
    console.log("Started Query for Admins");
    emptyAdmin();
    try {
        const URI = './api/schools/' + school_id + '/admins';
        console.log("URI: " + URI);
        const response = await fetch(URI);
        if (!response.ok) {
            throw new Error("Admins Unavailable At This Time!");
        }
        const admViewList = await response.json();
        console.log(JSON.stringify(admViewList));
        admViewList.map(admView => new AdministratorView(
            admView.adminID,
            admView.type,
            admView.username,
            admView.email,
            admView.surname,
            admView.phoneNumber,
            admView.birthDate,
            admView.givenNames,
            admView.schoolID,
            admView.employeeID)).forEach(adm => admViews.push(adm));
        console.log("All admins: " + JSON.stringify(admViews));
        for (const adm of admViews) {
            console.log("Each admin: " + JSON.stringify(adm));
            /** @type {AdministratorView} */
            const admObj = adm;
            const docElem = document.createElement('div');
            docElem.innerHTML = createDivAdmin(admObj);
            docElem.classList.add("form-box");
            schoolDiv.appendChild(docElem);
        }
    } catch (error) {
        console.log("An error has been produced with message");
        alert("Something went wrong, please try again later.")
    }
}

function addEventListenersForAdmin(adminID) {
    // Creating IDs for buttons:
    let viewID = "v" + adminID;
    console.log("The supposed id: " + viewID);
    let deleteID = "d" + adminID;
    console.log("The supposed id: " + deleteID);
    // Collecting buttons:
    const vButton = document.getElementById(viewID + "");
    const dButton = document.getElementById(deleteID + "");
    console.log("After accessing ADMIN");
    try {
        console.log("The actual id: " + vButton.id);
    } catch (error) {
        console.log(error);
    }
    console.log(dButton.id);
    vButton.addEventListener("click", function () {
        initializeViewAdmin(adminID);
    });
    dButton.addEventListener("click", function () {
        initializeUserDeletion(adminID);
    });
}
/**
 * Method will produce the query results and populate the necessary variables with the required information.
 * @returns {Promise<void>}
 */
async function querySchools() {
    // console.log("Started Query for Schools");
    // const title = document.createElement("h1");
    // title.innerHTML = createTitle("Schools");
    // mainDiv.appendChild(title);
    //make a div containing all the school divs
    clearDiv(mainDiv);
    initializeDashboard();
    await getAllAdmins();
    try {
        // const URI = './api/registrations/registrationViews/' + guardian_id;
        const URI = './api/schools/details';
        const response = await fetch(URI);
        if (!response.ok) {
            throw new Error("Schools Unavailable At This Time!");
        }
        const schViewList = await response.json();
        console.log("The whole thing from schools details: " + JSON.stringify(schViewList));
        schViewList.map(schView => new SchoolView(
            schView.school_id,
            schView.address_id,
            schView.name,
            schView.type,
            schView.phone_number,
            schView.email,
            schView.postalCode,
            schView.streetName,
            schView.streetNumber,
            schView.city,
            schView.country,
            schView.phoneNumber)).forEach(sch => schViews.push(sch));
        console.log("All schools: " + JSON.stringify(schViews));
        for (const sch of schViews) {
            console.log("Each school: " + JSON.stringify(sch));
            /** @type {SchoolView} */
            const schObj = sch;
            const docElem = document.createElement('div');
            docElem.innerHTML = createDivSchool(schObj);
            docElem.classList.add("form-box");
            await queryAdmins(sch.school_id, docElem);
            mainDiv.appendChild(docElem);
            // Creating IDs for buttons:
            let viewID = "v" + schObj.school_id;
            console.log(viewID);
            let deleteID = "d" + schObj.school_id;
            console.log(deleteID);
            let addID = "a" + schObj.school_id;
            console.log(addID);
            // Collecting buttons:
            const vButton = document.getElementById(viewID + "");
            const dButton = document.getElementById(deleteID + "");
            const aButton = document.getElementById(addID + "");
            const asButton = document.getElementById("add-school");
            console.log("After accessing School");
            console.log("The actual id for view: " + vButton.id);
            console.log("The actual id for delete: " + dButton.id);
            console.log("The actual id for add admin: " + aButton.id);
            console.log("The actual id for add school: " + asButton.id);
            vButton.addEventListener("click", function () {
                initializeViewSchool(schObj.school_id)
            });
            dButton.addEventListener("click", function () {
                initializeSchoolDeletion(schObj.address_id)
            });
            aButton.addEventListener("click", function () {
                changePagesAddSchoolAdmin(schObj.school_id);
            });
            console.log("Does it get here?")
            asButton.addEventListener("click", function () {
                changePagesAddSchool();
            });
            console.log("but here?")
            // dButton.addEventListener("click", function() {
            //     initializeEdit("" + regObj.registration_id)
            // });
            console.log("After eventListener for schools");
            for (const adm of admViews) {
                addEventListenersForAdmin(adm.adminID);
            }
            console.log("After eventListener for Admins");
        }
    } catch (error) {
        console.log("An error has been produced with message");
        alert("Something went wrong, please try again later.")
    }
    // title.innerHTML = createTitle("Administrators");
    // mainDiv.appendChild(title);
}
// BUTTON GENERATION --------------------------------------------------------------------------------------------------
function createDivSchool(schObj) {
    let viewID = "v" + schObj.school_id;
    let addID = "a" + schObj.school_id;
    let deleteID = "d" + schObj.school_id;
    console.log("School name:" + schObj.name);
    return `<div className="left" style="position: absolute;">
        <label>${schObj.name}</label>
        </div>
        <div className="right" style="margin-left: 625px; float: left; display: flex; position: absolute;">
        <button id = "${addID}" style="margin-right: 10px;">Add Admin</button>
        <button  id = "${viewID}" style="margin-right: 10px;">View School</button>
        <button id = "${deleteID}" style="margin-right: 10px;">Remove School</button>
        </div>`;
}

function createTitle(name) {
    return '<h1 style="margin-left: 21.025em; margin-top: 2.1875em;">' + name + '</h1>';
}

function createDivAdmin(admObj) {
    let viewID = "v" + admObj.adminID;
    let deleteID = "d" + admObj.adminID;
    console.log(`Admin Name: ${admObj.surname}`);
    console.log("View button id: " + viewID);
    return `<div className="left" style="margin-top: 50px; position: absolute; left: 260px;">
        <label>${admObj.surname}</label>
        </div>
        <div className="right" style="margin-top: 50px; position: absolute; margin-left: 715px;">
        <button  id = "${viewID}" style="margin-right: 10px;">View Admin</button>
        <button id = "${deleteID}" style="margin-right: 10px;">Remove Admin</button>
        </div>`;
}


/**
 * The button that is clicked, whose parent node ID is used to set the appropriate page status.
 * @param school_id
 */
function initializeViewSchool(school_id) {
    console.log(school_id);
    const sV = schViews.find(view => {
        return view.school_id === school_id;
    });
    sessionStorage.setItem("selectedSchool", JSON.stringify(sV));
    sessionStorage.setItem("pageStatus", PageStatus.ViewOnly.returnName());
    changePagesViewSchool();
}

function initializeViewAdmin(adminID) {
    console.log("the admin id for creating view " + adminID);
    const sV = allAdmins.find(view => {
        return view.adminID === adminID;
    });
    console.log("The admin view object " + sV.adminID)
    sessionStorage.setItem("selectedAdmin", JSON.stringify(sV));
    sessionStorage.setItem("pageStatus", PageStatus.ViewOnly.returnName());
    changePagesViewAdmin();
}
//DELETE METHODS
function initializeUserDeletion(id) {
    deleteAdmin(id).then(response => {
        if(response.ok) {
            console.log(response.text());
            alert('Successfully deleted');
        }
    }).catch(error => {
            console.error('Error:', error);
            alert('Failed to delete');
        });
    // try {
    //     const URI = "./api/users/" + id;
    //     const result = del(URI);
    //     console.log("the delete return for school: " + result.json);
    //     console.log("User deleted");
    //     //return result;
    // } catch (error) {
    //     console.log("error when delete request is made: " + error);
    // }
    //window.location.href = "/Topicus/topicusadmindashboard.html";
    //location.reload();
}
function initializeSchoolDeletion(address_id) {
    try {
        const URI = "./api/addresses/" + address_id;
        const result = del(URI);

        console.log("the delete return for school: " + result.json);
        console.log("Address deleted, on cascade school and then school admin");
        //return result;
    } catch (error) {
        console.log("error when delete request is made: " + error);
    }
    window.location.href = "/Topicus/topicusadmindashboard.html";

    //location.reload();
}
async function deleteAdmin(id) {
    const URI = `./api/users/${id}`;
    const options = {
        'method': 'DELETE'
    }
    const response = await fetch(URI, options);
    // const result = await response.text();
    // if (response.ok) {
    //     console.log(result);
    //     alert('Successfully deleted');
    // } else {
    //     alert('Failed to delete')
    // }
}
async function deleteSchool(id) {
    const URI = `./api/addresses/${id}`;
    const options = {
        'method': 'DELETE'
    }
    const response = await fetch(URI,options);
    const result = await response.text();
    if (response.ok) {
        console.log(result);
        alert('Successfully deleted');
    } else {
        alert('Failed to delete')
    }
}


