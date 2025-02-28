package src.client;

/**
 * Listens for incoming messages
 */
public abstract class Listener {

    /**
     * Displayes incoming messages
     */
    public abstract void recieveChatMessage();

    /**
     * Handles a disconnect from the connection, i.e., when the connection is closed.
     */
    public abstract void handleDisconnect();


}
