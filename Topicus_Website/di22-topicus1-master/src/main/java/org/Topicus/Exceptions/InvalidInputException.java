package org.Topicus.Exceptions;

public class InvalidInputException extends Exception {
    /**
     * Constructor used for the exception in the event that a token is not correct.
     * @param message will specify in what case.
     */
    public InvalidInputException(String message) {
        super(message);
    }
}