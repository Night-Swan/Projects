import { get } from "./requests.js";

const school_id = sessionStorage.getItem('selectedSchool');

window.addEventListener('load', loadDetailsAndRegistrations);
const content = document.getElementsByClassName('content')[0];

async function loadDetailsAndRegistrations() {
    const details_uri = `./api/schools/${school_id}`;
    const details = await get(details_uri);
    if (details !== undefined && details !== null) {
        console.log(details);
        const school_address_id = details.address_id;
        const school_address_uri = `./api/addresses/${school_address_id}`;
        const school_address = await get(school_address_uri);
        if (school_address !== undefined && school_address !== null) {
            console.log(school_address)
            details.school_address = school_address;
        }

        populateDetails(details);
    } else {
        const apology = document.createElement('h1');
        apology.textContent = "Currently, this school does not have any details available.\nApologies for the inconvenience!";
        content.appendChild(apology);
    }

    const URI = `./api/schools/${school_id}/forms/metadata`;
    const allRegistrationForms = await get(URI);
    if (allRegistrationForms !== undefined && allRegistrationForms !== null) {
        populateSchools(allRegistrationForms);
    } else {
        const apology = document.createElement('h1');
        apology.textContent = "Currently, this school does not have any active registration forms.\nApologies for the inconvenience!";
        content.appendChild(apology);
    }
}

function combineAddressDetails(address) {
    return `${address.streetNumber} ${address.streetName}, ${address.postalCode}, ${address.city}, ${address.country}`;
}

function populateDetails(details) {
    const formatted_address = combineAddressDetails(details.school_address);
    const name = details.name;
    const type = details.type;
    const phone_number = details.phone_number;
    const email = details.email;

    const section = document.createElement('section');
    const article = document.createElement('article');

    const h1 = document.createElement('h1');
    h1.textContent = name;

    const h2 = document.createElement('h2');
    h2.textContent = "School Type: " + type;

    const h3 = document.createElement('h3');
    h3.textContent = "Contact Phone Number: " + phone_number;

    const h3_2 = document.createElement('h3');
    h3_2.textContent = "Contact Email: " + email;

    const h3_3 = document.createElement('h3');
    h3_3.setAttribute('id', 'last_h3');
    h3_3.textContent = "School Address: " + formatted_address;

    article.appendChild(h1);
    article.appendChild(h2);
    article.appendChild(h3);
    article.appendChild(h3_2);
    article.appendChild(h3_3);
    section.appendChild(article);
    content.appendChild(section);
}

function populateSchools(registrationForms) {
    for (const registrationForm of registrationForms) {
        if (registrationForm.is_active) {
            content.appendChild(createRegistrationCard(registrationForm.title, registrationForm.registration_form_id));
        }
    }
}

function createRegistrationCard(title, id) {
    const section = document.createElement('section');
    const article = document.createElement('article');

    const h1 = document.createElement('h1');
    h1.textContent = title;

    const applyButton = document.createElement('a');
    applyButton.setAttribute('class', 'button');
    applyButton.setAttribute('id', id);
    applyButton.textContent = `Apply`;
    applyButton.addEventListener('click', function (event) {
        setSelectedRegistration(event, id);
    });

    article.appendChild(h1);
    article.appendChild(applyButton);
    section.appendChild(article);
    return section;
}

function setSelectedRegistration(event, registration_form_id) {
    event.preventDefault();
    sessionStorage.setItem("selectedRegistrationForm", registration_form_id);
    proceed();
}

function proceed() {
    window.location.href = "/Topicus/applyForRegistration.html";
}