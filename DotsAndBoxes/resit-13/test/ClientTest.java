package test;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import src.Server.ChatServer;
import src.client.Client;
import src.client.ClientConnection;
import src.client.UI;

import static org.junit.jupiter.api.Assertions.*;
import java.io.IOException;

public class ClientTest extends UI {

    private Client client;
    private Client client2;
    private String incoming;


    /**
     * Set up for the tests
     */
    @BeforeEach
    public void setUp() throws IOException {
        ChatServer chatServer = new ChatServer(4567);
        Thread t = new Thread(() -> {
            try {
                chatServer.acceptConnections();
            } catch (IOException e) {
                System.out.println(e);
            }
        });
        t.start();
        this.client = new Client(this);
        this.client.getProtocol().waitMessage();
        this.client2 = new Client(this);
        this.client.getProtocol().waitMessage();
//        this.client2.getProtocol().waitMessage();
        this.client2.sendLogin("Tali");
        this.client.getProtocol().waitMessage();
//        this.client2.getProtocol().waitMessage();
        this.client2.sendMessage("QUEUE");
    }

    /**
     * Test the initialization of a client
     * @throws IOException
     * @throws InterruptedException
     */
    @Test
    public void testClient() throws IOException, InterruptedException {
        this.client = new Client(this);
        this.client.getProtocol().waitMessage();
        assertEquals(incoming, "HELLO~DotsAndBoxesServer");

        this.client.sendLogin("Tali");
        this.client.getProtocol().waitMessage();
        assertEquals("ALREADYLOGGEDIN", incoming);

        this.client.sendLogin("Prez");
        this.client.getProtocol().waitMessage();
        assertEquals("LOGIN", incoming);

        this.client.sendMessage("LIST");
        this.client.getProtocol().waitMessage();
        assertTrue(incoming.equals("LIST~Tali~Prez") || incoming.equals("LIST~Prez~Tali"));

        this.client.sendMessage("HELP");
//        this.client.getProtocol().waitMessage();
        assertTrue(incoming.startsWith("HELP"));

        this.client.sendMessage("QUEUE");
        System.out.println("start waiting");
//        this.client.getProtocol().waitMessage();
        System.out.println("stoped waiting");
//
    }

    /**
     * Prints out the name of the current player in the game
     * @param name - name of current player
     */
    @Override
    public void notifyOfNewTurn(String name) {
    incoming = name;
    this.client.getProtocol().notifyOfMessage();
    }

    /**
     * Starts the user interface
     */
    @Override
    public void runUI() {

    }

    /**
     * Display the game board onto the current ui
     * @param board
     */
    @Override
    public void displayBoard(String board) {
        this.client.getProtocol().notifyOfMessage();
    incoming = board;
    }

    /**
     * Display messages incoming from the server and other game information
     * @param message - incoming message
     */
    @Override
    public synchronized void displayGameInfo(String message) {
        incoming = message;
        System.out.println(incoming);
        this.client.getProtocol().notifyOfMessage();
    }

    /**
     * Displays the NEWGAME message and does any appropriate action
     * @param message
     */
    @Override
    public synchronized void notifyNewGame(String message) {
        System.out.println("i'm still incoming");
        incoming = message;
        System.out.println(incoming);
        this.client.getProtocol().notifyOfMessage();
    }

    /**
     * Displayes the GAMEOVER message and does any appropriate action
     * @param message
     */
    @Override
    public void notifyGameOver(String message) {

    }

    /**
     * Asks the user for the address and port of the server they want to connect to
     */
    @Override
    public void askAddressandPort() {

    }

}
