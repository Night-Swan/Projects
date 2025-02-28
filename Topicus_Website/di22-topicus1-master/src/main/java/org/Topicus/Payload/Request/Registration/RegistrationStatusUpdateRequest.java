package org.Topicus.Payload.Request.Registration;

import java.util.UUID;

import org.Topicus.Model.Registration.Status;
import org.Topicus.Utility.Logs.LoggerManager;

import jakarta.xml.bind.annotation.XmlRootElement;

@XmlRootElement
public class RegistrationStatusUpdateRequest {
    // FIELD VARIABLE(S)
    // ---------------------------------------------------------------------------------------------
    private String registration_id;
    private String status;

    // CONSTRUCTOR(S)
    // ------------------------------------------------------------------------------------------------

    /**
     * Used to create an instance of the update request for the registration.
     * Validates whether status is acceptable.
     * 
     * @param registration_id
     * @param status
     */
    public RegistrationStatusUpdateRequest(String registration_id, String status) {
        this.registration_id = registration_id;
        this.status = status;
    }

    public RegistrationStatusUpdateRequest() {

    }

    // GETTER(S)
    // ----------------------------------------------------------------------------------------------------
    public String getRegistration_id() {
        return registration_id;
    }

    public String getStatus() {
        return status;
    }

    /**
     * Converts status to check if valid.
     * 
     * @returnof type Status.
     */
    public Status getConvertedStatus() {
        try {
            return Status.valueOf(status);
        } catch (IllegalArgumentException e) {
            LoggerManager.PAYLOAD_LOGGER.warning(this.status + " is not a valid Status");
            return null;
        }
    }

    /**
     * Converts UUID to check if valid.
     * 
     * @return of type UUID.
     */
    public UUID getConvertedUUID() {
        try {
            return UUID.fromString(registration_id);
        } catch (IllegalArgumentException e) {
            LoggerManager.PAYLOAD_LOGGER.warning(this.registration_id + " is not a valid UUID");
            return null;
        }
    }

    /**
     * If both parsed correctly, the request is valid on input.
     * 
     * @return of type boolean.
     */
    public boolean isValidRequest() {
        return (getConvertedStatus() != null && getConvertedUUID() != null);
    }
}
