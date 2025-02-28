package src.Server;

/**
 * Enum represents the different states of a server-client connection
 */
public enum ServerState {
    BEFORE_HELLO, RECEIVED_HELLO, RECEIVED_LOGIN, CONFIRMED_LOGIN, DURING_GAME
}


