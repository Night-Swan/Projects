import { getSessionSchoolID, getSessionUserType } from "./storageManagement.js";
import { get } from "./requests.js";

window.addEventListener('load', async function () {
    await populateSchoolPageDetails();
});

/**
 * @GET of the school by the schoolID stored in the fetched object of the currently logged-in School Admin.
 */
async function getSchool() {
    const URI = `./api/schools/${getSessionSchoolID()}`;
    const school = await get(URI);
    if (school !== null && school !== undefined) {
        return school;
    } else {
        alert('Something went wrong during retrieval of data!');
        throw new Error('Something went wrong during retrieval of data!');
    }
}

/**
 * Displays school's details and address details.
 */
async function populateSchoolPageDetails() {
    if (getSessionUserType() === 'SCHOOL_ADMIN') {
        const school = await getSchool();
        populateSchoolDetails(school);
        const address = await getAddress(school);
        populateAddressDetails(address);
    } else {
        alert('You are currently not logged in as a School Admin!');
        throw new Error('Access denied!');
    }
}

/**
 * Loads the school's details.
 * @param {object} school
 */
function populateSchoolDetails(school) {
    const fieldsSchool = document.getElementById('school').children;
    for (let i = 0; i <= 3; i++) {
        fieldsSchool[i].children[1].value = Object.values(school)[i + 2];
    }
}

/**
 * Loads the school address's details.
 * @param {object} school
 */
async function getAddress(school) {
    const URI = `./api/addresses/${school.address_id}`;
    const address = await get(URI);
    if (address !== null && address !== undefined) {
        return address;
    } else {
        alert('Something went wrong during retrieval of data!');
        throw new Error('Something went wrong during retrieval of data!');
    }
}

/**
 * Displays school's address details.
 * @param {object} address 
 */
function populateAddressDetails(address) {
    const fieldsSchool = document.getElementById('address').children;
    for (let i = 0; i <= 5; i++) {
        fieldsSchool[i].children[1].value = Object.values(address)[i + 1];
    }
}