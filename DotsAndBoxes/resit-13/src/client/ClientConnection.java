package src.client;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;
import java.util.concurrent.locks.ReentrantLock;

/**
 *  Class that represents a connection between the client and a server
 */
public class ClientConnection {

    private final Socket socket;
    private final BufferedReader in;
    private final BufferedWriter out;
    private boolean started;
    private ClientProtocol protocol;
    private static final String DESCRIPTION = "Client by Somone";

    public ClientConnection(Socket socket, ClientProtocol protocol) throws IOException {
        this.protocol = protocol;
        this.socket = socket;
        this.started = false;
        this.in = new BufferedReader(new InputStreamReader(socket.getInputStream()));
        this.out = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
        sendData(ClientProtocol.sendHello(DESCRIPTION));
    }

    public ClientConnection(InetAddress address, int port, ClientProtocol protocol) throws IOException {
        this(new Socket(address,port), protocol);
    }

    /**
     * Starts a listener thread that listenes for incoming messages from the server
     */
    //@ ensures \result != null;
    //@ ensures \result instanceof Listener;
    public Listener startGameListener() {
        if (started) {
            throw new IllegalStateException("Cannot start a SocketConnection twice");
        }
        started = true;
        Listener listener = new GameListener(protocol, in);
        Thread thread = new Thread(listener::recieveChatMessage);
        thread.start();
        return listener;
    }

    /**
     * Sends a message to the server.
     * @param data - The information that is to be sent to the server
     * @return true if the message has been successfully sent
     */
    //@ requires data != null;
    //@ ensures \result == (data != null);
    public boolean sendData(String data){
        try {
            System.out.println(data);
            out.write(data);
            out.newLine();
            out.flush();
            return true;
        } catch (IOException e) {
            System.out.println(e);
            return false;
        }
    }

}
