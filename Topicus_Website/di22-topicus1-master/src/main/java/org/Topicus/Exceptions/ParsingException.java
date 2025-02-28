package org.Topicus.Exceptions;

/**
 * Exception thrown when an error occurs when parsing.
 */
public class ParsingException extends Exception {
    // FIELD VARIABLE(S) --------------------------------------------------
    private final String objectType;
    private final String invalidField;

    /**
     * Informative exception constructor.
     * @param objectType representing object type.
     * @param invalidField representing incorrect field.
     * @param incorrectValue representing the invalid value yielded.
     */
    public ParsingException(String objectType, String invalidField, String incorrectValue) {
        super("Invalid for " + objectType + "| Invalid Field --> " + invalidField + "| Field Value: " + incorrectValue);
        this.objectType = objectType;
        this.invalidField = invalidField;
    }

    // GETTERS ---------------------------------------------------------------
    public String getObjectType() {
        return objectType;
    }

    public String getInvalidField() {
        return invalidField;
    }
}
