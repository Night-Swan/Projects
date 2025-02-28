package org.Topicus.Payload.Request.Registration;

import java.util.UUID;

import org.Topicus.Utility.Logs.LoggerManager;

import jakarta.xml.bind.annotation.XmlRootElement;

@XmlRootElement
public class FieldUpdateRequest {
    // FIELD VARIABLE(S)
    // ----------------------------------------------------------------------------------------------
    private String field_id;
    private String registration_id;
    private String content;

    // CONSTRUCTOR(S)
    // -----------------------------------------------------------------------------------
    public FieldUpdateRequest(String field_id, String registration_id, String content) {
        this.field_id = field_id;
        this.registration_id = registration_id;
        this.content = content;
    }

    public FieldUpdateRequest() {

    }
    // GETTER(S)
    // ------------------------------------------------------------------------

    public String getField_id() {
        return field_id;
    }

    public UUID getConvertedFieldID() {
        try {
            return UUID.fromString(field_id);
        } catch (IllegalArgumentException e) {
            LoggerManager.PAYLOAD_LOGGER.warning(this.field_id + " is not a valid UUID");
            return null;
        }
    }

    public String getRegistration_id() {
        return registration_id;
    }

    public UUID getConvertedRegistrationID() {
        try {
            return UUID.fromString(registration_id);
        } catch (IllegalArgumentException e) {
            LoggerManager.PAYLOAD_LOGGER.warning(this.registration_id + " is not a valid UUID");
            return null;
        }
    }

    public String getContent() {
        return content;
    }

    public boolean isValidRequest() {
        return (getConvertedFieldID() != null && getConvertedRegistrationID() != null);
    }
}
