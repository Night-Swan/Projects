package org.Topicus.Model.Registration;

import jakarta.xml.bind.annotation.XmlRootElement;
import org.Topicus.Model.RegistrationForm.DataType;

import java.util.UUID;

@XmlRootElement
public class FEDataField {
    // FIELD VARIABLE(S) -----------------------------------------------------------------------------------------------
    private UUID fieldID;
    private UUID registrationID;
    private UUID componentID;
    private UUID sectionID;
    private String title;
    private String content;
    private int position_number;

    private boolean mandatory;
    private String dataType;


    public FEDataField(UUID fieldID, UUID registrationID, UUID componentID, UUID sectionID, String title, String content, int position_number, boolean mandatory, String dataType) {
        this.fieldID = fieldID;
        this.registrationID = registrationID;
        this.componentID = componentID;
        this.sectionID = sectionID;
        this.title = title;
        this.content = content;
        this.position_number = position_number;
        this.mandatory = mandatory;
        this.dataType = dataType;
    }

    public FEDataField(UUID registrationID, UUID componentID, UUID sectionID, String title, String content, int position_number, boolean mandatory, String dataType) {
        this.registrationID = registrationID;
        this.componentID = componentID;
        this.sectionID = sectionID;
        this.title = title;
        this.content = content;
        this.position_number = position_number;
        this.mandatory = mandatory;
        // Setting Default Values in case Error:
        try {
            DataType dt = DataType.valueOf(dataType);
            this.dataType = dt.getValue();
        } catch (IllegalArgumentException e) {
            this.dataType = "TEXT";
        }
    }

    public UUID getFieldID() {
        return fieldID;
    }

    public UUID getRegistrationID() {
        return registrationID;
    }

    public UUID getComponentID() {
        return componentID;
    }

    public UUID getSectionID() {
        return sectionID;
    }

    public String getTitle() {
        return title;
    }

    public String getContent() {
        return content;
    }

    public int getPosition_number() {
        return position_number;
    }

    public boolean isMandatory() {
        return mandatory;
    }

    public String getDataType() {
        return dataType;
    }
}
