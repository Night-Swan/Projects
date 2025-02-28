package org.Topicus.Payload.Request.Registration;

import java.util.UUID;

public class FieldCreationRequest {
    // FIELD VARIABLE(S) ----------------------------------------------------------------
    private UUID registration_id;
    private UUID component_id;
    private String content;

    // CONSTRUCTOR(S) --------------------------------------------------------------------------------
    public FieldCreationRequest(UUID registration_id, UUID component_id, String content) {
        this.registration_id = registration_id;
        this.component_id = component_id;
        this.content = content;
    }

    public FieldCreationRequest() {
        
    }

    // GETTER(S) ---------------------------------------------------------------------------------------
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
