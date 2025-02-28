import {generateDescription} from "./formUtils.js";

/**
 * Initializes the styler and corresponding preview window when the page loads.
 * @type {initializeStyler}
 */
window.onload = initializeStyler();

/**
 * This method is used to initialize the styler components and button functionalities.
 */
function initializeStyler() {
    generateStylerDescription();
    initializeStylerButtons();
}

/**
 * This method is used to generate the description for the form styler.
 */
function generateStylerDescription() {
    document.getElementById("styler-desc").appendChild(generateDescription("Please use the styler below to style the registration form.", "description-text"));
}

/**
 * This method is used to initialize the buttons for the styler, adding their functionality.
 */
function initializeStylerButtons() {
    const colorSelector = document.getElementById("section-color-selector");
    colorSelector.addEventListener("change", () => {
        changeFontColorSection(colorSelector.value);
    });
    const colorSelectorComp = document.getElementById("comp-color-selector");
    colorSelectorComp.addEventListener("change", () => {
        changeFontColorComp(colorSelectorComp.value);
    });
    const backgroundSelector = document.getElementById("background-color-selector");
    backgroundSelector.addEventListener("change", () => {
        changeBackgroundColor(backgroundSelector.value);
    });
}

function changeFontColorSection(fcolor) {
    console.log(fcolor);
    sessionStorage.setItem("sectFontColor", "" + fcolor);
}

function changeFontColorComp(fcolor) {
    console.log(fcolor);
    sessionStorage.setItem("compFontColor", "" + fcolor);
}

function changeBackgroundColor(bcolor) {
    console.log(bcolor);
    sessionStorage.setItem("backColor", "" + bcolor);
}


