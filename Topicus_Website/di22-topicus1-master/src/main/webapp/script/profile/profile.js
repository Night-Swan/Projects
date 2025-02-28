import { getSessionGuardianID, getSessionUserID, getSessionUserType, isLoggedInWithAccount, isLoggedInWithAccountAndData, sessionWithGID } from "../storageManagement.js";
import { get, post, put } from "../requests.js";
import { inputSanitizer, isEmpty } from "../../fe_security/inputsanitizer.js";

window.addEventListener('load', getUserProfile);
hideElementsOnView(true, 0);
hideElementsOnView(true, 1);
hideElementsOnView(true, 2);

const tabProfile = document.getElementById('profile-data');
const tabChildren = document.getElementById('children');

const panelProfile = document.getElementById('panel-profile');
const panelChildren = document.getElementById('panel-children');
panelChildren.style.display = 'none';

tabProfile.addEventListener('click', displayProfilePanel);
tabChildren.addEventListener('click', displayChildrenPanel);

let user = {};
let guardian = {};
let address = {};
let child = { //mandatory contents - 7
    "childID": "",
    "surname": "",
    "givenNames": [],
    "preferredName": "",
    "birthDate": 0,
    "bsn": 0,
    "nationality": "",
    "languages": []
};

/**
 * Displays the appropriate sections of the form on click of a tab.
 * @param event
 */
function displayProfilePanel(event) {
    event.preventDefault();
    tabProfile.classList.add('active-tab');
    tabChildren.classList.remove('active-tab');
    panelProfile.style.display = 'block';
    panelChildren.style.display = 'none';

}

function displayChildrenPanel(event) {
    event.preventDefault();
    tabProfile.classList.remove('active-tab');
    tabChildren.classList.add('active-tab');
    panelProfile.style.display = 'none';
    panelChildren.style.display = 'block';
}

/**
 * @GET of the logged-in user's profile.
 * @returns {Promise<void>}
 */
async function getUserProfile() {
    if ((isLoggedInWithAccount() && ['SCHOOL_ADMIN', 'TOPICUS_ADMIN'].includes(getSessionUserType())) || isLoggedInWithAccountAndData()) {
        const userID = getSessionUserID();
        const URI = `./api/users/${userID}`;
        user = await get(URI);
        if (user !== undefined && user !== null) {
            await populateProfile();
        } else {
            alert('Something went wrong with retrieving your data!');
            window.location.href = "/Topicus/login.html";
        }
    } else {
        if (!sessionWithGID() || (isLoggedInWithAccount() && !isLoggedInWithAccountAndData() && getSessionUserType() === 'GUARDIAN')) {
            alert('You have not filled out your details!');
            window.location.href = "/Topicus/fillDetails.html";
        } else if (!isLoggedInWithAccount()) {
            alert('To view your profile, please login with an account or create one by linking it with your Guardian Code!');
            window.location.href = "/Topicus/login.html";
        }
    }
}

/**
 * Displays the user details and then calls the displays guardian and child details if the logged-in user is a guardian.
 * @returns {Promise<void>}
 */
async function populateProfile() {
    await populateUserDetails();
    if (getSessionUserType() === 'GUARDIAN') {
        await populateGuardianDetails();
        await populateChildrenDetails();
    } else {
        tabChildren.disabled = true;
        tabChildren.removeEventListener('click', displayChildrenPanel);
        document.getElementById('address').style.display = 'none';
        document.getElementById('guardian').style.display = 'none';
    }
}

/**
 * Hides form elements by index.
 * @param hide determines if the elements have to be hidden or not
 * @param i is 0, 1 or 2
 */
function hideElementsOnView(hide, i) {
    const confirmPasswordBlock = document.getElementById('block-confirm-password');
    const editButton = document.getElementsByClassName('edit-button')[i];
    const saveButton = document.getElementsByClassName('save-button')[i];
    const cancelButton = document.getElementsByClassName('cancel-button')[i];

    if (hide) {
        editButton.style.display = 'block';
        saveButton.style.display = 'none';
        cancelButton.style.display = 'none';
        if (i === 0) {
            confirmPasswordBlock.style.display = 'none';
            confirmPasswordBlock.children[1].value = '';
        }
    } else {
        editButton.style.display = 'none';
        saveButton.style.display = 'block';
        cancelButton.style.display = 'block';
        if (i === 0) {
            confirmPasswordBlock.style.display = 'block';
        }
    }
}

/**
 * Sets an input field to read-only.
 * @param box the input field
 */
function setBoxToReadOnly(box) {
    box.classList.remove('edit');
    box.classList.add('locked');
    box.readOnly = true;
}

/**
 * Sets an input field to edit-mode.
 * @param box the input field
 */
function setBoxToEditMode(box) {
    box.classList.remove('locked');
    box.classList.add('edit');
    box.readOnly = false;
}

/**
 * Sets the input fields of a section to read-only or edit-mode
 * @param fields to be set to read-only or to edit-mode
 * @param {true | false} readOnly
 */
function setBoxesToReadOnly(fields, readOnly) {
    if (readOnly) {
        for (const field of fields) {
            setBoxToReadOnly(field.children[1]);
        }
    } else {
        for (const field of fields) {
            setBoxToEditMode(field.children[1]);
        }
    }
}

/**
 * Cancels changes on 0) User 1) Address and Guardian 2) Child 3) Creating a Child.
 * @param i the identifier of the aforementioned
 */
function cancelChanges(i) {
    if (i === 0) {
        const userDetails = document.getElementsByClassName('user-detail');
        for (let i = 0; i <= 1 ; i++) {
            userDetails[i].children[1].value = Object.values(user)[i + 2];
        }
        userDetails[2].children[1].value = ''; //the password should be emptied
    } else if (i === 1) {
        const addressDetails = document.getElementsByClassName('address-detail');
        for (let i = 0; i < addressDetails.length; i++) {
            addressDetails[i].children[1].value = Object.values(address)[i + 1];
        }
        const guardianDetails = document.getElementsByClassName('guardian-detail');
        for (let i = 0; i < guardianDetails.length; i++) {
            const inputField = guardianDetails[i].children[1];
            const value = Object.values(guardian)[i + 3];
            if (i === 2) {
                inputField.value = value.join(' ');
            } else if (i === 4) {
                inputField.value = formatDate(value);
            } else {
                inputField.value = value;
            }
        }
    } else if (i === 2) {
        displayChildData();
    } else if (i === 3) {
        const createChildDetails = document.getElementsByClassName('create-child-detail');
        for (const createChildDetail of createChildDetails) {
            createChildDetail.children[1].value = '';
        }
        document.getElementById('create-child').style.display = 'none';
    }
}

/**
 * Formats the given date to the acceptable and readable form as in the Back-End.
 * @param timestamp the unformatted date
 * @returns {string} the formatted date
 */
function formatDate(timestamp) {
    const date = new Date(timestamp).toLocaleDateString('nl-NL', { day: '2-digit', month: '2-digit', year: 'numeric' });
    const date_tokens = date.split('-');
    return `${date_tokens[2]}-${date_tokens[1]}-${date_tokens[0]}`;
}

/**
 * Validates a field.
 * @param inputValue the input to be validated
 * @param label of the input field to create informative alert.
 */
function validateField(inputValue, label) {
    if (!inputSanitizer(inputValue) || isEmpty(inputValue)) {
        alert(`Your input for ${label} is invalid!`);
        throw new Error(`${inputValue} is an invalid input`);
    }
}

// ----- User -------
/**
 * Displays the data of the user.
 * @returns {Promise<void>}
 */
async function populateUserDetails() {
    hideElementsOnView(true, 0);
    const usernameBox = document.getElementById('username');
    const emailBox = document.getElementById('email'); //Password is unset on purpose!
    usernameBox.value = user.username;
    emailBox.value = user.email;

    const userDetails = document.getElementsByClassName('user-detail');
    document.getElementsByClassName('edit-button')[0].addEventListener('click', function () {
        setBoxesToReadOnly(userDetails, false);
        hideElementsOnView(false, 0);
    });
    document.getElementsByClassName('save-button')[0].addEventListener('click', async function (event) {
        const isUpdated = await updateAccount(event);
        if (isUpdated) {
            await populateUserDetails();
            setBoxesToReadOnly(userDetails, true);
            hideElementsOnView(true, 0);
            document.getElementById('password').value = '';
        }
    });
    document.getElementsByClassName('cancel-button')[0].addEventListener('click', function () {
        setBoxesToReadOnly(userDetails, true);
        cancelChanges(0);
        hideElementsOnView(true, 0);
    });
}

/**
 * @PUT request for the user. Please, note that the input password is not actually checked with the actual one if tit has been changed,
 * as it is received in hashed form from the Back-End for which we do not have a de-hashing function.
 * @param event
 * @returns {Promise<boolean|void>}
 */
async function updateAccount(event) {
    event.preventDefault();
    const changedUsername = document.getElementById('username').value; //Test if this actually works or have to get the boxes again...
    const changedEmail = document.getElementById('email').value;
    const changedPassword = document.getElementById('password').value;
    const confirmedPassword = document.getElementById('confirm-password').value;

    if (changedUsername !== user.username || changedEmail !== user.email) {
        if (inputSanitizer(changedUsername) && !isEmpty(changedUsername) && inputSanitizer(changedEmail) && !isEmpty(changedEmail) && inputSanitizer(changedPassword) && !isEmpty(changedPassword) && inputSanitizer(confirmedPassword)) {
            if (confirmedPassword !== changedPassword) {
                return alert('Passwords do not match!');
            } else {
                const URI = `./api/users/${getSessionUserID()}`;
                const userToUpdate = { "account_id": user.account_id, "type": user.type, "username": changedUsername, "email": changedEmail, "password_value": changedPassword };
                const updatedUser = await put(URI, userToUpdate);
                if (updatedUser !== undefined && updatedUser !== null) {
                    user = updatedUser;
                    alert('You have successfully updated your account!');
                    return true;
                } else {
                    alert('Oh no! The update of your account failed!');
                    return false;
                }
            }
        } else {
            alert('Invalid input!');
            return false;
        }
    }
    return false;
}

//  -----Address-----
/**
 * @GET request for the address.
 * @returns {Promise<*>}
 */
async function populateAddressDetails() {
    const URI = `./api/addresses/${guardian.address_id}`;
    address = await get(URI);
    if (address !== undefined && address !== null) {
        const addressDetails = document.getElementsByClassName('address-detail');
        for (let i = 0; i <= 5; i++) {
            const value = Object.values(address)[i + 1];
            const inputField = addressDetails[i].children[1];
            inputField.value = value;
        }
        return address;
    } else {
        throw new Error('Could not retrieve address data!');
    }
}

/**
 * @PUT request for the address.
 * @param event
 * @returns {Promise<boolean>}
 */
async function updateAddress(event) {
    const addressDetails = document.getElementsByClassName('address-detail');
    let isChanged = false;
    let addressToUpdate = { 'addressID': address.addressID };
    for (let i = 0; i < addressDetails.length; i++) {
        const inputValue = addressDetails[i].children[1].value;
        const [key, value] = Object.entries(address)[i + 1];
        validateField(inputValue, addressDetails[i].children[0].textContent);
        if (i === 2 && isNaN(Number(inputValue))) {
            alert('The input of Street Number is not a number!');
            throw new Error('Invalid Street Number!');
        } else if (i === 2 && Number(inputValue) !== value) {
            isChanged = true;
            addressToUpdate[key] = Number(inputValue);
            continue;
        } else if (inputValue !== value) {
            isChanged = true;
        }
        addressToUpdate[key] = inputValue;
    }

    if (isChanged) {
        addressToUpdate["streetNumber"] = Number(addressToUpdate["streetNumber"]);
        if (isNaN(addressToUpdate["streetNumber"])) {
            alert('Street Number is not a number!');
            throw new Error('Street Number is not a number!');
        }
        const URI = `./api/addresses/${address.addressID}`;
        const updatedAddress = await put(URI, addressToUpdate);
        if (updatedAddress !== undefined && updatedAddress !== null) {
            address = updatedAddress;
            return true;
        } else {
            alert('Oh no! The update of your address details failed!');
            return false;
        }
    }
    return false;
}

// -----Guardian------
/**
 * @GET request for the guardian.
 * @returns {Promise<void>}
 */
async function populateGuardianDetails() {
    const URI = `./api/parents/${getSessionGuardianID()}`;
    guardian = await get(URI);
    address = await populateAddressDetails();
    if (guardian !== undefined && guardian !== null) {
        const guardianDetails = document.getElementsByClassName('guardian-detail');
        for (let i = 0; i <= 6; i++) {
            const [key, value] = Object.entries(guardian)[i + 3];
            const inputField = guardianDetails[i].children[1];
            if (key === "given_names") {
                inputField.value = value.join(' ');
            } else if (key === "date_of_birth") {
                inputField.value = formatDate(value);
            } else {
                inputField.value = value;
            }
        }
        setGuardianButtonsFunctionality();
    } else {
        throw new Error('There is no guardian linked to that account!');
    }
}

/**
 * Sets the appropriate button functionality to the Personal Details section.
 */
function setGuardianButtonsFunctionality() {
    const guardianDetails = document.getElementsByClassName('guardian-detail');
    const addressDetails = document.getElementsByClassName('address-detail');
    document.getElementsByClassName('edit-button')[1].addEventListener('click', function () {
        setBoxesToReadOnly(addressDetails, false);
        setBoxesToReadOnly(guardianDetails, false);
        hideElementsOnView(false, 1);
    });
    document.getElementsByClassName('save-button')[1].addEventListener('click', async function (event) {
        const isUpdatedAddress = await updateAddress(event);
        const isUpdatedGuardian = await updateGuardian(event);
        if (isUpdatedAddress || isUpdatedGuardian) {
            if (isUpdatedAddress) {
                alert('You have successfully updated your address details!');
            } else if (isUpdatedGuardian) {
                alert('You have successfully updated your guardian details!');
            }

            setBoxesToReadOnly(addressDetails, true);
            setBoxesToReadOnly(guardianDetails, true);
            hideElementsOnView(true, 1);
        }
    });
    document.getElementsByClassName('cancel-button')[1].addEventListener('click', function () {
        setBoxesToReadOnly(addressDetails, true);
        setBoxesToReadOnly(guardianDetails, true);
        cancelChanges(1);
        hideElementsOnView(true, 1);
    });
}

/**
 * @PUT request for the guardian.
 * @param event
 * @returns {Promise<boolean>}
 */
async function updateGuardian(event) {
    const guardianDetails = document.getElementsByClassName('guardian-detail');
    let isChanged = false;
    const guardianToUpdate = { 'guardian_id': guardian.guardian_id, 'account_id': guardian.account_id, 'address_id': guardian.address_id};
    for (let i = 0; i < guardianDetails.length; i++) {
        const inputValue = guardianDetails[i].children[1].value;
        const [key, value] = Object.entries(guardian)[i + 3];
        validateField(inputValue, guardianDetails[i].children[0].textContent);
        if (isNaN(Number(inputValue))) {
            alert('The input of Street Number is not a number!');
            throw new Error('Invalid Street Number!');
        } else if (i === 2 && Number(inputValue) !== value) {
            isChanged = true;
        } else if (inputValue !== value) {
            isChanged = true;
        }
        guardianToUpdate[key] = inputValue;
    }

    if (isChanged) {
        guardianToUpdate["given_names"] = guardianToUpdate["given_names"].split(',').map(x => x.trim()).join(' ').split(' ');
        const URI = `./api/parents/${guardian.guardian_id}`;
        const updatedGuardian = await put(URI, guardianToUpdate);
        if (updatedGuardian !== undefined && updatedGuardian !== null) {
            guardian = updatedGuardian;
            return true;
        } else {
            alert('Oh no! The update of your guardian details failed!');
            return false;
        }
    }
    return false;
}

// ------ Child -------
/**
 * @GET request for all children by a guardian ID.
 * @returns {Promise<void>}
 */
async function populateChildrenDetails() {
    const gid = getSessionGuardianID();
    if (gid !== undefined && gid !== null && gid !== '') {
        const URI = `./api/parents/${gid}/children`;
        const children = await get(URI);
        await loadDropdown(children);
    }
}

/**
 * Loads the dropdown with all children of a guardian if there are any, otherwise stays hidden and only the Add Child option is displayed.
 * @GET for a chosen child of the logged in guardian whom they have chosen from the dropdown.
 * @param children
 */
async function loadDropdown(children) {
    hideElementsOnView(true, 2);
    const selectBlock = document.getElementById('childOptions');
    selectBlock.innerText = '';
    if (children === undefined || children === null || children.length === 0) {
        document.getElementById('dropdown').style.display = 'none';
        document.getElementsByClassName('footer-buttons')[2].style.display = 'none';
        const info = document.getElementsByClassName('info')[1];
        info.innerHTML = `&#9432; You do not have any registered children!<br>Add them below.`;
        info.style.display = 'block';

        const childDetail = document.getElementsByClassName('child-detail');
        for (const childDetailElement of childDetail) {
            childDetailElement.style.display = 'none';
        }
        const addButton = document.getElementsByClassName('add-button')[0];
        const editButton = document.getElementsByClassName('edit-button')[2];
        addButton.style.display = 'block';
        editButton.style.display = 'none';
        setCreateChildButtonsFunctionality();
    } else {
        for (const child1 of children) {
            const option = document.createElement("option");
            option.value = child1.childID;
            option.textContent = child1.givenNames.join(' ') + ' ' + child1.surname;
            selectBlock.appendChild(option);
        }

        if (children.length === 1) {
            await updateFormChildDetails(null, children[0].childID);
        }
        selectBlock.addEventListener('change', async function (event) {
            await updateFormChildDetails(event, this.value);
        });
    }
}

/**
 * @GET request to display the child details in the input fields.
 * @param {Event} event
 * @param {string} value
 */
async function updateFormChildDetails(event, value) {
    if (event !== null) {
        event.preventDefault();
    }
    const selectBlock = document.getElementById('childOptions');
    if (value !== undefined && value !== null && value !== '') {
        selectBlock.disabled = true;
        setTimeout(function () {
            // Unlock the selectBlock element after 500ms
            selectBlock.disabled = false;
        }, 500);

        const URI = `./api/children/${value}`;
        child = await get(URI);
        displayChildData();
        setChildButtonsFunctionality();
    }
}

/**
 * Displays the data of a selected child from the dropdown in the input fields.
 */
function displayChildData() {
    const childDetails = document.getElementsByClassName('child-detail');
    for (let i = 0; i < childDetails.length; i++) {
        const [key, value] = Object.entries(child)[i + 1];
        const inputField = childDetails[i].children[1];
        if (["givenNames", "languages"].includes(key)) {
            inputField.value = value.join(' ');
        } else if (key === "bsn") {
            inputField.value = Number(value);
        } else if (key === "birthDate") {
            inputField.value = formatDate(Number(value));
        } else {
            inputField.value = value;
        }
    }
}

/**
 * Adds the event listeners to the buttons related to the child tab of the form.
 */
function setChildButtonsFunctionality() {
    const childDetails = document.getElementsByClassName('child-detail');
    document.getElementsByClassName('edit-button')[2].addEventListener('click', function () {
        const info = document.getElementsByClassName('info')[1];
        info.style.display = 'none';
        setBoxesToReadOnly(childDetails, false);
        hideElementsOnView(false, 2);
    });
    document.getElementsByClassName('save-button')[2].addEventListener('click', async function (event) {
        const isUpdated = await updateChild(event);
        if (isUpdated) {
            await populateChildrenDetails();
            setBoxesToReadOnly(childDetails, true);
            hideElementsOnView(true, 2);
        }
    });
    document.getElementsByClassName('cancel-button')[2].addEventListener('click', function () {
        setBoxesToReadOnly(childDetails, true);
        cancelChanges(2);
        hideElementsOnView(true, 2);
    });
    setCreateChildButtonsFunctionality();
}

function setCreateChildButtonsFunctionality() {
    document.getElementsByClassName('add-button')[0].addEventListener('click', async function (event) {
        const createChildBlockDisplay = document.getElementById('create-child').style.display;
        if (createChildBlockDisplay === 'none') {
            createChildView();
        } else {
            const isCreated = await createChild(event);
            if (isCreated) {
                await populateChildrenDetails();
                createChildView();
            }
        }
    });
    document.getElementsByClassName('cancel-button')[3].addEventListener('click', function () {
        cancelChanges(3);
        this.style.display = 'none';
    });
}

/**
 * @PUT request for the selected child.
 * @param event
 * @returns {Promise<boolean>}
 */
async function updateChild(event) {
    const childDetails = document.getElementsByClassName('child-detail');
    let isChanged = false;
    const selectBlock = document.getElementById('childOptions');
    const childID = selectBlock.options[selectBlock.selectedIndex].value;
    let childToUpdate = { 'childID': childID };
    for (let i = 0; i < childDetails.length; i++) {
        const inputValue = childDetails[i].children[1].value;
        const [key, value] = Object.entries(child)[i + 1]; //not sure if +1 or +2
        console.log(Object.entries(child)[i + 1])
        validateField(inputValue, childDetails[i].children[0].textContent);
        if (inputValue !== value) {
            isChanged = true;
        }
        if (["givenNames", "languages"].includes(key)) {
            childToUpdate[key] = inputValue.split(' ');
        } else if (key === "bsn") {
            childToUpdate[key] = Number(inputValue);
            if (isNaN(childToUpdate[key])) {
                alert('BSN is not a number!');
                throw new Error('BSN is not a number!');
            }
        } else {
            childToUpdate[key] = inputValue;
        }
    }

    if (isChanged) {
        const info = document.getElementsByClassName('info')[1];
        info.style.display = 'block';
        const URI = `./api/children/${childID}`;
        const updatedChild = await put(URI, childToUpdate);
        if (updatedChild !== undefined && updatedChild !== null) {
            child = updatedChild;
            info.innerHTML = `&#9432; Successfully updated child details!`;
            return true;
        } else {
            info.textContent = 'Oh no! The update of your child details failed!';
            return false;
        }
    }
    return false;
}

/**
 * @POST request when a guardian wants to add a new child.
 * @param event
 * @returns {Promise<boolean>}
 */
async function createChild(event) {
    event.preventDefault();
    const URI = `./api/children`;
    const childToCreate = { "guardianId": getSessionGuardianID()};
    const createChildDetails = document.getElementsByClassName('create-child-detail');

    for (let i = 0; i < createChildDetails.length; i++) {
        const input = createChildDetails[i].children[1].value;
        const label = createChildDetails[i].children[0].textContent;
        validateField(input, label);
        const key = Object.keys(child)[i + 1];
        if (["givenNames", "languages"].includes(key)) {
            childToCreate[key] = input.split(' ');
        } else if (key === "bsn") {
            childToCreate[key] = Number(input);
        } else {
            childToCreate[key] = input;
        }
    }
    const createdChild = await post(URI, childToCreate);
    if (createdChild !== undefined && createdChild !== null) {
        alert('Successfully added!\n\nPlease, refresh if this is your first ever added child!');
        return true;
    } else {
        alert('Child creation failed, please, try again!');
        throw new Error('POST of child failed');
    }
}

/**
 * Initializes the 'create child view' or hides it.
 */
function createChildView() {
    const createChildBlock = document.getElementById('create-child');
    const cancelButton = document.getElementsByClassName('cancel-button')[3];
    if (createChildBlock.style.display === 'none') {
        createChildBlock.style.display = 'block';
        cancelButton.style.display = 'block';
    } else {
        createChildBlock.style.display = 'none';
        const createChildDetails = document.getElementsByClassName('create-child-detail');
        for (const createChildDetail of createChildDetails) {
            createChildDetail.children[1].value = '';
        }
        cancelButton.style.display = 'none';
    }
}