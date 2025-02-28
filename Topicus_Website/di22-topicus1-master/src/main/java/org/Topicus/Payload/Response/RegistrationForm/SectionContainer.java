package org.Topicus.Payload.Response.RegistrationForm;

import java.util.List;

import org.Topicus.Model.RegistrationForm.FormComponent;
import org.Topicus.Model.RegistrationForm.Section;

import jakarta.xml.bind.annotation.XmlRootElement;

@XmlRootElement
public class SectionContainer {
    private Section section;
    private List<FormComponent> formComponentList;

    public SectionContainer() {

    }
    
    public SectionContainer(Section section, List<FormComponent> formComponentList) {
        this.section = section;
        this.formComponentList = formComponentList;
    }

    public Section getSection() {
        return section;
    }

    public void setSection(Section section) {
        this.section = section;
    }

    public List<FormComponent> getFormComponentList() {
        return formComponentList;
    }

    public void setFormComponentList(List<FormComponent> formComponentList) {
        this.formComponentList = formComponentList;
    }
}
