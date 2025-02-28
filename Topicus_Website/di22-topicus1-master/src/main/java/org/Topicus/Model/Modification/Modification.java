package org.Topicus.Model.Modification;

import jakarta.xml.bind.annotation.XmlRootElement;

import java.sql.Date;
import java.util.UUID;
@XmlRootElement
public class Modification {
    // FIELD VARIABLE(S) --------------------------------------------------------------------------------------
    private UUID mod_id;
    private UUID sa_id;
    private UUID reg_id;
    private String description;
    private String date;
    private boolean visible;

    // CONSTRUCTOR(S) -----------------------------------------------------------------------------------------

    /**
     * Fully loaded constructor for a Modification object.
     * @param mod_id
     * @param sa_id
     * @param reg_id
     * @param description
     * @param date
     * @param visible
     */
    public Modification(UUID mod_id, UUID sa_id, UUID reg_id, String description, Date date, boolean visible) {
        this.mod_id = mod_id;
        this.sa_id = sa_id;
        this.reg_id = reg_id;
        this.description = description;
        this.date = date.toString();
        this.visible = visible;
    }

    // GETTER(S) ----------------------------------------------------------------------------------------------

    public UUID getMod_id() {
        return mod_id;
    }

    public UUID getSa_id() {
        return sa_id;
    }

    public UUID getReg_id() {
        return reg_id;
    }

    public String getDescription() {
        return description;
    }

    public String getDate() {
        return date;
    }

    public boolean isVisible() {
        return visible;
    }
}
