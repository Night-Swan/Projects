package org.Topicus.Model.RegistrationForm;

public enum DataType {
    TEXT("Text"), DATE("Date"), FILE("File"), IMAGE("Image"), NUMBER("Number");

    // FIELD VARIABLES -------------------------------------------------------------------------------------------------
    private String value;

    // CONSTRUCTOR -----------------------------------------------------------------------------------------------------
    DataType(String value) {
        this.value = value;
    }

    // GETTER ----------------------------------------------------------------------------------------------------------
    public String getValue() {
        return value;
    }
}
