import { get } from "./requests.js";
import {inputSanitizer, isEmpty} from "../fe_security/inputsanitizer.js";

window.addEventListener('load', loadSchools);
let allSchools = [];

const searchInput = document.getElementById('search-input');
searchInput.addEventListener('keyup', displaySuggestions);

function displaySuggestions() {
    clearSchoolForms();
    const term = searchInput.value;
    if (!isEmpty(term) && inputSanitizer(term)) {
        const filteredSchools = allSchools.filter(a => a.name.toLowerCase().includes(term.toLowerCase()));
        populateSchools(filteredSchools);
    } else if (isEmpty(term)) {
        populateSchools(allSchools);
    }
}

function clearSchoolForms() {
    document.getElementById('school-forms').innerText = '';
}

async function loadSchools() {
    const URI = "./api/schools";
    allSchools = await get(URI);
    populateSchools(allSchools);
}

function populateSchools(schools) {
    const schoolForms = document.getElementById('school-forms');
    schoolForms.addEventListener('click', function (event) {
        fillSearchBar(event);
    });
    for (const school of schools) { //photos have to be added
        schoolForms.appendChild(createSchoolCard(school.name, school.type, school.school_id));
    }
}

function createSchoolCard(name, type, school_id) {
    const schoolBox = document.createElement('div');
    schoolBox.setAttribute('class', 'school-box');

    const schoolPhoto = document.createElement('div');
    schoolPhoto.setAttribute('class', 'school-photo');
    schoolPhoto.style.backgroundImage = "url('https://i.insider.com/56df0582dd0895d3708b45d0?width=1200&format=jpeg')";

    const schoolName = document.createElement('div');
    schoolName.setAttribute('class', 'school-name');
    schoolName.textContent = `${name}`;

    const schoolType = document.createElement('div');
    schoolType.setAttribute('class', 'school-type');
    schoolType.textContent = `${type}`;

    const applyButton = document.createElement('a');
    applyButton.setAttribute('class', 'button');
    applyButton.setAttribute('id', school_id);
    applyButton.textContent = `Choose`;
    
    schoolBox.appendChild(schoolPhoto);
    schoolBox.appendChild(schoolName);
    schoolBox.appendChild(schoolType);
    schoolBox.appendChild(applyButton);
    return schoolBox;
}

function fillSearchBar(event) {
    if (event.target.classList.contains('button')) {
        const school_id = event.target.id;
        setSelectedSchool(school_id);
    } else {
        const name = event.target.parentElement.getElementsByClassName('school-name')[0].textContent;
        searchInput.value = name;
    }
}

function setSelectedSchool(school_id) {
    sessionStorage.setItem("selectedSchool", school_id);
    proceed();
}

function proceed() {
    window.location.href = "/Topicus/chooseRegistration.html";
}