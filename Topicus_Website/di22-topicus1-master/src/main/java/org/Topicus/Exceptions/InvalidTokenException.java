package org.Topicus.Exceptions;

public class InvalidTokenException extends Exception {
    /**
     * Constructor used for the exception in the event that a token is not correct.
     * @param message will specify in what case.
     */
    public InvalidTokenException(String message) {
        super(message);
    }
}
