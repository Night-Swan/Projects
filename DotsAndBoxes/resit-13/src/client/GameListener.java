package src.client;

import src.Server.ClientHandler;

import java.io.BufferedReader;
import java.io.IOException;

public class GameListener extends Listener{

    private ClientProtocol protocol;
    private BufferedReader in;

    private String incoming;
    public GameListener(ClientProtocol protocol, BufferedReader in) {
//        super();
        this.in = in;
        this.protocol = protocol;
    }

    /**
     * Receives messages from the server
     */
    //@ ensures incoming != null;
    @Override
    public void recieveChatMessage() {
        try {
            while ((incoming = in.readLine()) != null) {
                handleMessage(incoming);
            }
        } catch (IOException e) {
            // ignore the exception, just close the connection
        }
    }

    /**
     * Hanndle the incoming message
     * @param incoming - message from the server that has to be handeled
     */
    //@ requires incoming != null;
    private void handleMessage(String incoming) {
        protocol.handleIncoming(incoming);
    }

    /**
     * Handles a disconnect from the connection, i.e., when the connection is closed.
     */
    @Override
    public void handleDisconnect() {

    }
}
