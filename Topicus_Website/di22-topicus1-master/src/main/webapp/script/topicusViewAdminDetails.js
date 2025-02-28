// OBJECTS -------------------------------------------------------------------------------------
const admView = JSON.parse(sessionStorage.getItem("selectedAdmin"));

window.addEventListener("load", async function() {
    if (window.location.pathname.includes("/Topicus/topicusviewschooladmin.html")) {
        insertValues();
    }
});

let d = document.getElementById("back-button");
d.addEventListener("click", function() {
    window.location.href = '/Topicus/topicusadmindashboard.html';
});

function insertValues() {
    console.log("The admin view : " + admView);
    let d = document.getElementById("givenNames");
    d.value = admView.givenNames;

    d = document.getElementById("lastname");
    d.value = admView.surname;

    d = document.getElementById("email");
    d.value = admView.email;

    d = document.getElementById("phone");
    d.value = admView.phoneNumber;

    d = document.getElementById("username");
    d.value = admView.username;

    d = document.getElementById("birthDate");
    d.value = formatDate(admView.birthDate);

    let back = document.getElementById("back-button");
    back.addEventListener("click", function() {
        window.location.href = '/Topicus/topicusadmindashboard.html';
    });
}

const formatDate = timestamp => new Date(timestamp).toLocaleDateString('nl-NL', { day: '2-digit', month: '2-digit', year: 'numeric' }).split('-').reverse().join('-');