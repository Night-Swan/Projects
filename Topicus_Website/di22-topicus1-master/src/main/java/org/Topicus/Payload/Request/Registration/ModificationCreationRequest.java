package org.Topicus.Payload.Request.Registration;

import java.sql.Date;
import java.util.UUID;

import org.Topicus.Utility.Logs.LoggerManager;
import org.Topicus.Utility.Parsers.UUIDParser;

import jakarta.xml.bind.annotation.XmlRootElement;

@XmlRootElement
public class ModificationCreationRequest implements UUIDParser {
    // FIELD VARIABLE(S)
    // -----------------------------------------------------------------------------------------------
    private String sa_id;
    private String reg_id;
    private String description;
    private Date date;
    private boolean visibility;

    // CONSTRUCTOR(S)
    // --------------------------------------------------------------------------------------------------
    public ModificationCreationRequest() {

    }

    public ModificationCreationRequest(String sa_id, String reg_id, String description, String visibility) {
        this.sa_id = sa_id;
        this.reg_id = reg_id;
        this.description = description;
        this.date = new Date(System.currentTimeMillis());

        try {
            this.visibility = Boolean.parseBoolean(visibility);
        } catch (IllegalArgumentException e) {
            LoggerManager.PAYLOAD_LOGGER.warning(visibility + " is not a valid boolean value");
            this.visibility = false;
        }
    }

    public String getSa_id() {
        return sa_id;
    }

    public UUID getConvertedSA_ID() {
        return convertFromString(getSa_id());
    }

    public String getReg_id() {
        return reg_id;
    }

    public UUID getConvertedREG_ID() {
        return convertFromString(getReg_id());
    }

    public String getDescription() {
        return description;
    }

    public Date getDate() {
        return date;
    }

    public void setVisibility(boolean visibility) {
        this.visibility = visibility;
    }

    public boolean isVisible() {
        return visibility;
    }

    public boolean isValidRequest() {
        return (getConvertedREG_ID() != null && getConvertedSA_ID() != null);
    }
}
