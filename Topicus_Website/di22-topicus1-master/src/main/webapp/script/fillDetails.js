import { inputSanitizer, isEmpty } from "../fe_security/inputsanitizer.js";
import { post } from "./requests.js";
import { setSessionGuardianID } from "./storageManagement.js"; //login: martin00 martin00@gmail.com pass

document.getElementById('save-button').addEventListener('click', createObjects);

const address = { // length = 6 - mandatory fields
    "postalCode": "",
    "streetName": "",
    "streetNumber": "",
    "city": "",
    "country": "",
    "phoneNumber": ""
};

const guardian = { // length = 7 - mandatory fields
    "address_id": "",
    "nationality": "",
    "surname": "",
    "given_names": [],
    "phone_number": "",
    "birth_date": "1989-09-01",
    "occupation": "",
    "company_name": ""
};

function beginApplicationProcess() {
    window.location.href = "/Topicus/schools.html";
}

/**
 * Creates the address and guardian objects.
 * @param {Event} event 
 */
async function createObjects(event) { // 6 for address and 7 for guardian
    event.preventDefault();
    const inputFields = document.getElementsByTagName('input');

    for (let i = 0; i < inputFields.length; i++) {
        const input = inputFields[i].value;
        if (inputSanitizer(input) && !isEmpty(input)) {
            if (i < 6 && !address.addressID) {
                const addressAttribute = Object.keys(address)[i];
                address[addressAttribute] = input;
            } else {
                const guardianAttribute = Object.keys(guardian)[i - 5]; // begin with nationality
                if (i - 5 === 3) {
                    guardian[guardianAttribute] = input.split(' ');
                } else {
                    guardian[guardianAttribute] = input;
                }
            }
        }
    }
    if (!address["addressID"]) {
        await createAddress();
    }
    await createGuardian(address.addressID);

    if (guardian["guardian_id"]) {
        setSessionGuardianID(guardian["guardian_id"]);
        alert('Success!');
        displayMyProfileButton();
        beginApplicationProcess();
    } else {
        throw new Error('Creation of guardian went wrong!');
    }
}

/**
 * Creates the Address object.
 * @returns {string} addressID for the creation of the Guardian
 */
async function createAddress() {
    const URI = "./api/addresses";
    const data = await post(URI, address);
    console.log("ADDRESS ID:  " + data.addressID);
    address["addressID"] = data.addressID;
}

/**
 * Creates the guardian after filling out the Guardian Details form.
 * @param {string} address_id
 */
async function createGuardian(address_id) {
    guardian["address_id"] = address_id;
    const URI = "./api/parents";
    const data = await post(URI, guardian);
    console.log("GUARDIAN ID:  " + data.guardian_id);
    guardian["guardian_id"] = data.guardian_id;
}

function displayMyProfileButton() {
    const nav = document.getElementById('navigation');
    const divProfile = nav.children[nav.childElementCount - 2].children[0];
    const profileButton = divProfile.children[0];
    profileButton.style.display = 'block';
}