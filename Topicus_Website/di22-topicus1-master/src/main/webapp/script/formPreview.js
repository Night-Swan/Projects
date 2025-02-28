import {SentSection, SentComponent, prepareSectionsComponents, scl_list} from "./registrationFormBuilder.js";

window.onload = initializePreviewButton();

/**
 * This method is used to add the functionality for the preview.
 */
function initializePreviewButton() {
    document.getElementById("form-preview-start").addEventListener("click", () => {
        initializePreview();
    });
}

/**
 * This method is used to produce the preview in the small window.
 */
function initializePreview() {
    document.getElementById("preview-space").innerHTML = "";
    prepareSectionsComponents();
    const listOfSectionContainers = scl_list;
    const sectFontColor = sessionStorage.getItem("sectFontColor");
    const compFontColor = sessionStorage.getItem("compFontColor");
    const backColor = sessionStorage.getItem("backColor");
    console.log(sectFontColor, compFontColor, backColor);
    producePreview(listOfSectionContainers);
    applyFormatting(sectFontColor, compFontColor, backColor);
}

/**
 * This method is used to produce the text for the mini-preview.
 */
function producePreview(listOfSectionContainers) {
    const previewSpace = document.getElementById("preview-space");
    previewSpace.innerHTML = "";
    previewSpace.appendChild(createText(listOfSectionContainers));
}

/**
 * This method is used to create the text.
 * @param listOfSectionContainers
 */
function createText(listOfSectionContainers) {
    const list = document.createElement("ol");
    list.setAttribute("id", "preview-list");
    console.log(JSON.stringify(listOfSectionContainers));
    for (const sectionContainer of listOfSectionContainers) {
        /**@type {SectionContainer} */
        const container = sectionContainer;
        sectionToHTML(container.section, container.formComponents, list);
    }
    console.log("Complete");
    return list;
}

/**
 * This method is used to parse a section to HTML, including the sublist.
 * @param section
 * @param componentsList
 * @param listOfSections
 */
function sectionToHTML(section, componentsList, listOfSections) {
    /**@type {SentSection} */
    const sec = section;
    const secItem = document.createElement("li");
    secItem.setAttribute("class", "sec-prev");
    secItem.innerText = `${sec.title}`;
    const sublist = document.createElement("ul");
    sublist.setAttribute("class", "comp-sublist");
    console.log(JSON.stringify(sec));
    for (const comp of componentsList) {
        /**@type {SentComponent} */
        const component = comp;
        componentToHTML(component, sublist);
    }
    secItem.appendChild(sublist);
    listOfSections.appendChild(secItem);
}

/**
 * This method is used to parse the component to HTML.
 * @param comp
 * @param sublist
 */
function componentToHTML(comp, sublist) {
    /**@type {SentComponent} */
    const com = comp;
    const elem = document.createElement("li");
    elem.setAttribute("class", "comp-prev");
    elem.innerText = `${com.title} [${com.data_type}, ${com.mandatory}]`;
    sublist.appendChild(elem);
}

/**
 * This method is used to implement the styling.
 * @param sectFontColor
 * @param compFontColor
 * @param backColor
 */
function applyFormatting(sectFontColor, compFontColor, backColor) {
    applySectFontColor(sectFontColor);
    applyCompFontColor(compFontColor);
    applyBackColor(backColor);
}

/**
 * This method is used to apply the font colors for the section.
 * @param sectFontColor
 */
function applySectFontColor(sectFontColor) {
    if (sectFontColor !== null && sectFontColor !== undefined && sectFontColor !== "") {
        document.getElementById("preview-list").style.color = sectFontColor;
    }
}

/**
 * This method is used to apply the font color for the sublist.
 * @param compFontColor
 */
function applyCompFontColor(compFontColor) {
    if (compFontColor !== null && compFontColor !== undefined && compFontColor !== "") {
        const sublists = document.getElementsByClassName("comp-sublist");
        for (const sublist of sublists) {
            sublist.style.color = compFontColor;
        }
    }
}

/**
 * This method is used to apply the background color.
 * @param backColor
 */
function applyBackColor(backColor) {
    if (backColor !== null && backColor !== undefined && backColor !== "") {
        const previewSpace = document.getElementById("preview-space");
        previewSpace.style.backgroundColor = backColor;
    }
}