package org.Topicus.Exceptions;

/**
 * Exception to define Connection Construction issues in ConnectionBuilder.
 */
public class ConnectionConstructionException extends Exception {
    /**
     * Exception constructor.
     * @param message of type String, representing message.
     */
    public ConnectionConstructionException(String message) {
        super(message);
    }
}
