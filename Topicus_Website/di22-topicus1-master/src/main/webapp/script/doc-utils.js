const { jsPDF } = window.jspdf;

/**
 * Creates a PDF document from the given form.
 * 
 * @param {*} form the HTMLFormElement object from which the PDF will be generated
 */
function formToPDF(form) {
    const doc = new jsPDF();

    // Define the styling variables
    const titleFontSize = 20;
    const sectionFontSize = 16;
    const labelFontSize = 12;
    const valueFontSize = 12;
    const lineHeight = 15;
    const margin = 20;
    const boxWidth = 170;
    const boxMargin = 5;
    const pageXCenter = doc.internal.pageSize.getWidth() / 2;

    // Set initial vertical position (y coordinate)
    let y = margin;

    // Add title
    const title = form.querySelector('#registration-form-title').innerText;
    doc.setFontSize(titleFontSize);
    doc.setFont('helvetica', 'bold');
    doc.text(title, margin, y);
    y += lineHeight * 2;

    // Loop through each section
    const sectionsElement = form.querySelector('#sections');
    const sections = sectionsElement.querySelectorAll('.section');

    sections.forEach((section) => {
        // Add section header
        const sectionTitleLabel = section.querySelector('p');
        const sectionTitle = sectionTitleLabel.innerText;
        doc.setFontSize(sectionFontSize);
        doc.setFont('helvetica', 'bold');

        // Center the section title
        const pageWidth = doc.internal.pageSize.getWidth();
        const textWidth = doc.getStringUnitWidth(sectionTitle) * sectionFontSize / doc.internal.scaleFactor;
        const textOffset = (pageWidth - textWidth) / 2;
        doc.text(sectionTitle, textOffset, y);
        y += lineHeight * 2;

        const componentsElement = section.querySelector('.section-form-components');
        const components = componentsElement.querySelectorAll('.form-component');
        components.forEach((component) => {
            const label = component.querySelector('label');
            const input = component.querySelector('input');

            // Get the label and input values
            const name = label.innerText;
            const value = input.value;

            // Check if the content exceeds the page height
            const pageHeight = doc.internal.pageSize.getHeight();
            if (y + lineHeight > pageHeight - margin) {
                doc.addPage(); // Add a new page
                y = margin; // Reset the vertical position
            }

            // Calculate the component height based on the number of lines
            const linesCount = Math.max(name.split('\n').length, value.split('\n').length);
            const componentHeight = lineHeight * linesCount + boxMargin * 2;

            // Add the joined box for the component name and value
            doc.setDrawColor(0);
            doc.setFillColor(255, 255, 255);
            doc.rect(margin, y, boxWidth, componentHeight, 'FD');

            // Calculate the vertical position for centered alignment
            const boxCenterY = y + componentHeight / 2;

            // Add the vertical line between the two boxes
            const verticalLineX = margin + boxWidth / 2;
            doc.setLineWidth(0.5);
            doc.line(verticalLineX, y, verticalLineX, y + componentHeight);

            // Add the component name inside the first half of the joined box
            doc.setFontSize(labelFontSize);
            doc.setFont('helvetica', 'bold');
            const nameX = pageXCenter - boxWidth / 4;

            doc.text(name, nameX, boxCenterY, { align: 'center', baseline: 'middle' });

            // Add the component value inside the second half of the joined box
            doc.setFontSize(valueFontSize);
            doc.setFont('helvetica', 'normal');
            const valueX = pageXCenter + boxWidth / 4;
            doc.text(value, valueX, boxCenterY, { align: 'center', baseline: 'middle' });

            // Increment the vertical position
            y += componentHeight;
        });

        // Add spacing between sections
        y += lineHeight * 2;
    });

    // Save the PDF
    doc.save('registration_form.pdf');
}

function registrationToPDF(registration_form_html_component) {
    const doc = new jsPDF();

    // Define the styling variables
    const titleFontSize = 20;
    const sectionFontSize = 16;
    const labelFontSize = 12;
    const valueFontSize = 12;
    const lineHeight = 15;
    const margin = 20;
    const boxWidth = 170;
    const boxMargin = 5;
    const pageXCenter = doc.internal.pageSize.getWidth() / 2;
    let first_section = true;

    // Set initial vertical position (y coordinate)
    let y = margin;

    // Add title
    const title = 'Registration Form';
    doc.setFontSize(titleFontSize);
    doc.setFont('helvetica', 'bold');
    doc.text(title, margin, y);
    y += lineHeight * 2;

    const children = registration_form_html_component.children;

    for (let i = 0; i < children.length; i++) {
        const child = children[i];
        if (child.tagName === 'P') {
            if (first_section) {
                first_section = false;
            } else {
                y += lineHeight * 2;
            }

            const sectionTitle = child.innerText;
            doc.setFontSize(sectionFontSize);
            doc.setFont('helvetica', 'bold');

            // Center the section title
            const pageWidth = doc.internal.pageSize.getWidth();
            const textWidth = doc.getStringUnitWidth(sectionTitle) * sectionFontSize / doc.internal.scaleFactor;
            const textOffset = (pageWidth - textWidth) / 2;
            doc.text(sectionTitle, textOffset, y);
            y += lineHeight * 2;
        } else if (child.tagName === 'SPAN') {
            const label = child.querySelector('label');
            const input = child.querySelector('input');

            // Get the label and input values
            const name = label.innerText;
            const value = input.value;

            // Check if the content exceeds the page height
            const pageHeight = doc.internal.pageSize.getHeight();
            if (y + lineHeight > pageHeight - margin) {
                doc.addPage(); // Add a new page
                y = margin; // Reset the vertical position
            }

            // Calculate the component height based on the number of lines
            const linesCount = Math.max(name.split('\n').length, value.split('\n').length);
            const componentHeight = lineHeight * linesCount + boxMargin * 2;

            // Add the joined box for the component name and value
            doc.setDrawColor(0);
            doc.setFillColor(255, 255, 255);
            doc.rect(margin, y, boxWidth, componentHeight, 'FD');

            // Calculate the vertical position for centered alignment
            const boxCenterY = y + componentHeight / 2;

            // Add the vertical line between the two boxes
            const verticalLineX = margin + boxWidth / 2;
            doc.setLineWidth(0.5);
            doc.line(verticalLineX, y, verticalLineX, y + componentHeight);

            // Add the component name inside the first half of the joined box
            doc.setFontSize(labelFontSize);
            doc.setFont('helvetica', 'bold');
            const nameX = pageXCenter - boxWidth / 4;

            doc.text(name, nameX, boxCenterY, { align: 'center', baseline: 'middle' });

            // Add the component value inside the second half of the joined box
            doc.setFontSize(valueFontSize);
            doc.setFont('helvetica', 'normal');
            const valueX = pageXCenter + boxWidth / 4;
            doc.text(value, valueX, boxCenterY, { align: 'center', baseline: 'middle' });

            // Increment the vertical position
            y += componentHeight;
        }
    }

    // Save the PDF
    doc.save('registration_form.pdf');
}

async function exportRegistrationsToCsv(form_id) {
    const uri = "./api/registrations/export/" + form_id;
    const response = await fetch(uri);
    if (!response.ok) {
        console.log("Invalid Response");
        alert("Download failed: try again later.");
    } else {
        try {
            const data = await response.json();
            let csv_export = createCsvExport(data);
            downloadFile(csv_export);
        } catch(Error) {
            alert("Something went wrong, please try again later.");
        }

    }

    // fetch(uri).then(response => response.json()).then(registrations => {
    //     console.log(registrations);
    //     let csv_export = createCsvExport(registrations);
    //     downloadFile(csv_export);
    // });
}

function createCsvExport(registrations) {
    let csv_export = getCsvFormatFromRegistrations(registrations);
    return new File([csv_export], "registrations.csv");
}

function downloadFile(file) {
    const link = document.createElement("a");
    link.style.display = "none";
    link.href = URL.createObjectURL(file);
    link.download = file.name;
    document.body.appendChild(link);
    link.click();

    setTimeout(() => {
        URL.revokeObjectURL(link.href);
        link.parentNode.removeChild(link);
    }, 0);
}

function getCsvFormatFromRegistrations(registrations) {
    let registrations_csv = "";
    registrations_csv += "STATUS, ";
    let stripped = stripRegistrationContainer(registrations[1]);
    stripped.sections.forEach(section => {
        registrations_csv += section.title.toUpperCase() + ", ";

        section.data_fields.forEach(data_field => {
            registrations_csv += data_field.title + ", ";
        });
    });
    registrations_csv += "\n";
    registrations.forEach(registration => {
        registrations_csv += registrationToCsv(stripRegistrationContainer(registration));
    });

    return registrations_csv;
}

function registrationToCsv(registration) {
    let registration_csv = "";
    registration_csv += registration.status + ",";
    registration.sections.forEach(section => {
        registration_csv += ",";
        section.data_fields.forEach(data_field => {
            registration_csv += data_field.content + ",";
        })
    });
    registration_csv += "\n";

    return registration_csv;
}

function stripRegistrationContainer(reg_cont) {
    let stripped = {};
    stripped.status = reg_cont.reg.status;
    stripped.sections = [];
    reg_cont.sections.forEach(section => {
        let stripped_section = {};
        stripped_section.title = section.title;
        stripped_section.position_number = section.position_number;
        stripped_section.data_fields = getSortedDataFieldsForSection(section.section_id, reg_cont.df_pos);
        stripped.sections.push(stripped_section);
    });

    stripped.sections.sort((a, b) => {
        return a.position_number - b.position_number;
    });

    return stripped;
}

function getSortedDataFieldsForSection(section_id, data_fields) {
    let sorted_data_fields = [];
    data_fields.forEach(data_field => {
        if (data_field.sectionID === section_id) {
            sorted_data_fields.push(stripDataField(data_field));
        }
    });

    sorted_data_fields.sort((a, b) => {
        return a.position_number - b.position_number;
    });

    return sorted_data_fields;
}

function stripDataField(data_field) {
    let stripped = {};
    stripped.title = data_field.title;
    stripped.content = data_field.content;
    stripped.position_number = data_field.position_number;
    return stripped;
}
