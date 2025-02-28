package org.Topicus.Payload.Response.Registration;

import java.util.UUID;

public class ModificationListView {
    // FIELD VARIABLE(S) ------------------------------------------------------------------------------------
    private String date;
    private UUID sa_id;
    private String surname;
    private UUID reg_id;
    private String description;
    private boolean visibility;

    // CONSTRUCTOR(S) --------------------------------------------------------------------------------------
    public ModificationListView() {

    }

    public ModificationListView(String date, UUID sa_id, String surname, UUID reg_id, String description, boolean visibility) {
        this.date = date;
        this.sa_id = sa_id;
        this.surname = surname;
        this.reg_id = reg_id;
        this.description = description;
        this.visibility = visibility;
    }

    // GETTER(S) -------------------------------------------------------------------------------------------
    public String getDate() {
        return date;
    }

    public UUID getSa_id() {
        return sa_id;
    }

    public String getSurname() {
        return surname;
    }

    public UUID getReg_id() {
        return reg_id;
    }

    public String getDescription() {
        return description;
    }

    public boolean isVisible() {
        return visibility;
    }
}
