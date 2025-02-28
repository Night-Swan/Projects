import { inputSanitizer, isEmpty} from "../fe_security/inputsanitizer.js";

const form = document.getElementById("contact-form");
form.addEventListener("submit", onSubmit);
const button = document.getElementById("add-school");
button.addEventListener("click",function() {
    window.location.href = '/Topicus/topicusadmindashboard.html';
})

async function createAddress(addressData) {
    try {
        console.log("The json for address: " + JSON.stringify(addressData));
        const response = await fetch("./api/addresses", {
            method: "POST",
            headers: {
                "Content-Type": "application/json",
            },
            body: JSON.stringify(addressData),
        });

        if (response.ok) {
            const addressResult = await response.json();
            return addressResult;
            alert("Address added");
        } else {
            console.error("Error adding address for school:", response.status);
        }
    } catch (error) {
        console.error("There is an error:", error);
    }
}

async function createSchool(schoolData) {
    try {
        console.log("The json for school: " + JSON.stringify(schoolData));
        const response = await fetch("./api/schools", {
            method: "POST",
            headers: {
                "Content-Type": "application/json",
            },
            body: JSON.stringify(schoolData),
        });

        if (response.ok) {
            alert("School added");
        } else {
            alert("Error, school not added")
            console.error("Error adding school:", response.status);
        }
    } catch (error) {
        console.error("There is an error:", error);
    }
}

async function onSubmit(event) {
    event.preventDefault();
    //here after we have all the field( address and the ones for school)
    //addr
    const postalCode = document.getElementById("address-postalCode").value;
    const streetName = document.getElementById("address-streetName").value;
    const streetNumber = document.getElementById("address-streetNumber").value;
    const city = document.getElementById("address-city").value;
    const country = document.getElementById("address-country").value;
    const phoneNumber = document.getElementById("address-phoneNumber").value;
    //schDetails
    const name = document.getElementById("school-name").value;
    const type = document.getElementById("school-type").value;
    // const schoolAddress = document.getElementById("school-address").value;
    const phone_number = document.getElementById("phone-number").value;
    const email = document.getElementById("e-mail").value;

    console.log(postalCode + " | " + streetName + " | " + streetNumber + " | "  + city + " | "  + country + " | "  + phoneNumber + " | "
     + name + " | "  + type + " | "  + phone_number + " | " + email);

    if (isEmpty(postalCode) || isEmpty(streetName) || isEmpty(streetNumber) || isEmpty(city) || isEmpty(country) ||
        isEmpty(phoneNumber) || isEmpty(name) || isEmpty(type) || isEmpty(phone_number) || isEmpty(email)) {
        return alert("An input field is empty!");}
    // } else if (
    //     inputSanitizer(postalCode) ||
    //     inputSanitizer(streetName) ||
    //     inputSanitizer(streetNumber) ||
    //     inputSanitizer(city) ||
    //     inputSanitizer(country) ||
    //     inputSanitizer(phoneNumber) ||
    //     inputSanitizer(name) ||
    //     inputSanitizer(type) ||
    //     inputSanitizer(phone_number) ||
    //     inputSanitizer(email)
    // ) {
    //     return alert("One of your fields is invalid. Please try again");
    // }
    const addressData = {
        postalCode,
        streetName,
        streetNumber,
        city,
        country,
        phoneNumber
    }
    const addressResult = await createAddress(addressData);
    console.log(addressResult);
    const address_id = addressResult.addressID;
    console.log(addressResult.addressID);
    const schoolData = {
        address_id,
        name,
        type,
        phone_number,
        email,
    };
    await createSchool(schoolData);
    window.location.href = 'http://localhost:8080/Topicus/topicusadmindashboard.html';
}
