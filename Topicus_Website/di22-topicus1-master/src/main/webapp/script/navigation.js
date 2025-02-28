import { clearSession, clearSessionGuardianID, hasSession, isLoggedInWithAccount, isLoggedInWithAccountAndData, sessionWithGID, getSessionUserType } from "./storageManagement.js";
import { FormStatus } from "./formUtils.js";
export { updateNavOnLoad, updateNavOnSession };

const navigation = document.getElementById("navigation");
const sticky = navigation.offsetTop;

if (getSessionUserType() === 'SCHOOL_ADMIN') {
    navigation.getElementsByClassName('roles')[0].children[3].addEventListener('click', function () {
        sessionStorage.setItem("formStatus", FormStatus.Generate.returnName());
        window.location.href = "/Topicus/registrationadmin.html";
    });
}

/**
 * Makes the navigation stick to the top of the page with width 100%.
 */
function stickNav() {
    if (window.pageYOffset > sticky) {
        navigation.classList.add("sticky");
    } else {
        navigation.classList.remove("sticky");
    }
}

window.onscroll = function () {
    stickNav();
}

document.getElementById('logoutBtn').addEventListener('click', onLogout);
updateNavOnLoad(); //login enforcements:
//checkBodyOnLoadLoggedIn();
//checkPageByRole(); - NOT WORKING
checkFilledDetails();

/**
 * Updates the navigation according to the user state.
 */
function updateNavOnLoad() {
    updateNavOnSession();
    if (hasSession()) {
        navigation.querySelector('.user').style.display = 'block';
        navigation.querySelector('.guest').style.display = 'none';
    } else {
        navigation.querySelector('.user').style.display = 'none';
        navigation.querySelector('.guest').style.display = 'block';
    }
}

/**
 * Updates the navigation once - after logging in, otherwise the navigation will become crammed up with buttons and will flicker too much
 * if the same methodology as in updateNavOnLoad is used. It is used only for the Profile page, however, it can still be used for all pages, but it will cause flickering.
 */
function updateNavOnSession() {
    if (window.location.pathname.includes('/Topicus/myprofile.html') && isLoggedInWithAccount()) { //Only for My Profile
        removeRoleButtons();
        populateButtonsByRole();
    }
}

/**
 * Removes all buttons in regard to roles. Does not alter .guest and .user.
 */
function removeRoleButtons() {
    const role = navigation.children[0]; // roles
    while (role.firstChild) {
        role.removeChild(role.firstChild);
    }
}

/**
 * Populates the navigation role buttons according to the user type.
 */
function populateButtonsByRole() {
    const userType = getSessionUserType();
    const dashboardButton = document.createElement('a');
    dashboardButton.textContent = 'Dashboard';
    if (userType === 'GUARDIAN' || sessionWithGID()) { // 0 - Home, 1 - Dashboard, 2 - Apply for Registration
        const homeButton = document.createElement('a');
        homeButton.setAttribute('href', "/Topicus/home.html"); //SET SCHOOL PAGE
        homeButton.textContent = "Home";
        dashboardButton.setAttribute('href', "/Topicus/dashboard.html");
        const applyForRegistrationButton = document.createElement('a');
        applyForRegistrationButton.setAttribute('href', "/Topicus/schools.html");
        applyForRegistrationButton.textContent = "Apply for Registration";

        const guardianButtons = [homeButton, dashboardButton, applyForRegistrationButton];
        appendRoleButtons(guardianButtons);
    } else if (userType === 'SCHOOL_ADMIN') { // School Page, Dashboard, Forms, Logout
        const schoolPageButton = document.createElement('a');
        schoolPageButton.setAttribute('href', "/Topicus/schoolPage.html"); //SET SCHOOL PAGE
        schoolPageButton.textContent = "School Page";
        dashboardButton.setAttribute('href', "/Topicus/schooladmindashboard.html");
        const formsButton = document.createElement('a');
        formsButton.setAttribute('href', "/Topicus/viewSchoolForms.html");
        formsButton.textContent = "Forms";
        const createFormButton = document.createElement('a');
        createFormButton.setAttribute('href', "/Topicus/registrationadmin.html");
        createFormButton.textContent = "Create Form";

        const schoolAdminButtons = [schoolPageButton, dashboardButton, formsButton, createFormButton];
        appendRoleButtons(schoolAdminButtons);
    } else if (userType === 'TOPICUS_ADMIN') { // School Management, Dashboard, School Administrators
        const schoolManagementButton = document.createElement('a');
        schoolManagementButton.setAttribute('href', "/Topicus/topicusAddSchool.html");
        schoolManagementButton.textContent = "School Management";
        dashboardButton.setAttribute('href', "/Topicus/topicusadmindashboard.html");
        const schoolAdministratorsButton = document.createElement('a');
        schoolAdministratorsButton.setAttribute('href', "/Topicus/topicusaddschooladmin.html");
        schoolAdministratorsButton.textContent = "School Administrators";

        const topicusAdminButtons = [schoolManagementButton, dashboardButton, schoolAdministratorsButton];
        appendRoleButtons(topicusAdminButtons);
    }
}

/**
 * Appends the buttons to the navigation according to the user role.
 * @param {Array} updatedNavRoleButtons the buttons to be appended
 */
function appendRoleButtons(updatedNavRoleButtons) {
    const role = navigation.children[0];
    for (const roleButton of updatedNavRoleButtons) {
        role.appendChild(roleButton);
    }
}

/**
 * When the user is not logged and the location is not Login/Home (2 paths)/Sign up/Schools - all other pages are prohibited
 * Extended with referrers - a user can go to schools, however they can only go to chooseRegistration only after being to schools. Same with applyForRegistration
 */
function checkBodyOnLoadLoggedIn() {
    const isNotAllowedDirectPage = !window.location.pathname.includes("/Topicus/login.html") && !window.location.pathname.includes("/Topicus/home.html") && !window.location.pathname.includes("/Topicus/signup.html");
    const isNotAllowedReferrerPage = !(window.location.pathname.includes("/Topicus/schools.html") && document.referrer.includes("/Topicus/login.html")) && !(window.location.pathname.includes("/Topicus/chooseRegistration.html") && document.referrer.includes("/Topicus/schools.html")) && !(window.location.pathname.includes("/Topicus/applyForRegistration.html") && document.referrer.includes("/Topicus/chooseRegistration.html"));
    if (!hasSession() && isNotAllowedDirectPage && isNotAllowedReferrerPage) {
        window.location.href = "/Topicus/login.html";
    }
}

/**
 * Prohibits the user from leaving the Fill Details page before successfully filling out the form.
 */
function checkFilledDetails() {
    if (document.referrer.includes("/Topicus/fillDetails.html") && isLoggedInWithAccount() && !isLoggedInWithAccountAndData()) {
        alert('Please, input your details before you proceed!');
        window.location.href = "/Topicus/fillDetails.html";
    }
}

function checkPageByRole() {
    const guardianPages = ["/applyForRegistration", "/chooseRegistration", "/dashboard", "/fillDetails", "/home", "/schools", "/viewRegistrationParent"];
    const schoolAdminPages = ["/registrationadmin", "/schooladmindashboard", "/schoolPage", "/viewFormSchoolAdmin", "/viewRegistrationSchAdmin", "viewSchoolForms"];
    //const topicusAdminPages = ["/topicusAddSchool", "/topicusaddschooladmin", "/topicusadmindashboard", "/topicusViewSchool", "/topicusviewschooladmin"];
    const userType = getSessionUserType();
    const splitPage = window.location.href.split("/");
    const page = "/" + splitPage[splitPage.length - 1].replace(".html", "");
    const roleChecker = (userType !== 'GUARDIAN' && guardianPages.includes(page)) || (userType !== 'SCHOOL_ADMIN' && schoolAdminPages.includes(page) && userType !== "PUBLIC");
    if (roleChecker) {
        const ref = document.referrer;
        console.log(ref)
        const refSplit = ref.split("/");
        console.log(refSplit);
        const formattedRef = "/" + refSplit.splice(refSplit.length - 2).join("/");
        console.log(formattedRef);
        alert("Access denied!");
        throw new Error(formattedRef);
        //window.location.href = formattedRef;
    }
}

/**
 * Clears a cookie by setting its expiration date to the past.
 * @param {*} cookieName 
 */
function clearCookie(cookieName) {
    document.cookie = cookieName + "=; expires=Thu, 01 Jan 1970 00:00:00 UTC; path=/;";
}

/**
 * Clears all stored data during the session, updates the navigation and redirects to Home.
 */
function onLogout() {
    clearSession();
    clearSessionGuardianID();
    clearCookie("authorization_token");
    updateNavOnLoad();
    window.location.href = "/Topicus/home.html";
}