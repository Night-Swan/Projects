package org.Topicus.Model.Registration;

import jakarta.xml.bind.annotation.XmlRootElement;

import java.util.UUID;

@XmlRootElement
public class DBDataField {
    // FIELD VARIABLE(S) ------------------------------------------------------------------------------
    private UUID field_id;
    private UUID registration_id;
    private UUID component_id;
    private String content;

    // CONSTRUCTOR(S) ----------------------------------------------------------------------------------------

    /**
     * Fully loaded constructor for parsing a data field from the back-end (DB) to the front-end.
     * @param field_id
     * @param registration_id
     * @param component_id
     * @param content
     */
    public DBDataField(UUID field_id, UUID registration_id, UUID component_id, String content) {
        this.field_id = field_id;
        this.registration_id = registration_id;
        this.component_id = component_id;
        this.content = content;
    }

    // GETTER(S) ----------------------------------------------------------------------------------------------

    public UUID getField_id() {
        return field_id;
    }

    public UUID getRegistration_id() {
        return registration_id;
    }

    public UUID getComponent_id() {
        return component_id;
    }

    public String getContent() {
        return content;
    }
}
