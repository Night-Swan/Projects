// OBJECTS -------------------------------------------------------------------------------------
const schView = JSON.parse(sessionStorage.getItem("selectedSchool"));
window.addEventListener("load", async function() {
    if (window.location.pathname.includes("/Topicus/topicusViewSchool.html")) {
        insertValues();
    }
});
const back = document.getElementById("back-button");
back.addEventListener("click", function() {
    window.location.href = '/Topicus/topicusadmindashboard.html';
});
function insertValues() {
    let d = document.getElementById("school-name");
    d.value = schView.name;

    d = document.getElementById("school-type");
    d.value = schView.type;

    d = document.getElementById("phone-number");
    d.value = schView.phone_number;

    d = document.getElementById("e-mail");
    d.value = schView.email;

    d = document.getElementById("address-postalCode");
    d.value = schView.postalCode;

    d = document.getElementById("address-streetName");
    d.value = schView.streetName;

    d = document.getElementById("address-streetNumber");
    d.value = schView.streetNumber;

    d = document.getElementById("address-city");
    d.value = schView.city;

    d = document.getElementById("address-country");
    d.value = schView.country;

    d = document.getElementById("address-phoneNumber");
    d.value = schView.phoneNumber;

}