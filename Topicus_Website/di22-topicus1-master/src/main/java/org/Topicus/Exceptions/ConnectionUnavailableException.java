package org.Topicus.Exceptions;

/**
 * Exception defined to show that a ConnectionPackage's connection is not available.
 */
public class ConnectionUnavailableException extends Exception {
    // CONSTRUCTOR(S) -----------------------------------------
    public ConnectionUnavailableException(String message) {
        super(message);
    }
}
