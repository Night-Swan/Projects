package org.Topicus.Payload.Response.School;

public class SchoolName {
    // FIELD VARIABLE(S) ---------------------------------------------------------
    private String name;
    private String type;
    // CONSTRUCTOR(S) -------------------------------------------------------------

    public SchoolName(String name,String type) {
        this.name = name;
        this.type = type;
    }

    // GETTER(S) --------------------------------------------------------------------


    public String getName() {
        return name;
    }

    public String getType() {
        return type;
    }
}
