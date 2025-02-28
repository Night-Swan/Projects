package org.Topicus.Payload.Response.RegistrationForm;

import java.util.List;

import org.Topicus.Model.RegistrationForm.RegistrationFormMetadata;
import org.Topicus.Model.RegistrationForm.Style.Style;

import jakarta.xml.bind.annotation.XmlRootElement;

@XmlRootElement
public class RegistrationFormContainer {
    private RegistrationFormMetadata formMetadata;
    private List<SectionContainer> sectionContainerList;
    private Style formStyle;

    public RegistrationFormContainer() {

    }
    
    public RegistrationFormContainer(RegistrationFormMetadata form, List<SectionContainer> sectionContainerList, Style formStyle) {
        this.formMetadata = form;
        this.sectionContainerList = sectionContainerList;
        this.formStyle = formStyle;
    }

    public RegistrationFormMetadata getFormMetadata() {
        return formMetadata;
    }

    public void setFormMetadata(RegistrationFormMetadata form) {
        this.formMetadata = form;
    }

    public List<SectionContainer> getSectionContainerList() {
        return sectionContainerList;
    }

    public void setSectionContainerList(List<SectionContainer> sectionContainerList) {
        this.sectionContainerList = sectionContainerList;
    }

    public Style getFormStyle() {
        return formStyle;
    }

    public void setFormStyle(Style formStyle) {
        this.formStyle = formStyle;
    }
}
