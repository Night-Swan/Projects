package src.client;

import java.io.IOException;
import java.util.concurrent.locks.ReentrantLock;

/**
 * Abstract version of the ui used for generalizing
 */
public abstract class UI {

    private Client client;
    private ReentrantLock lock;

    /**
     * Starts a client
     * @throws IOException
     */
    public void startClient() throws IOException {
        this.client = new Client(this);
    }

    /**
     * Prints out the name of the current player in the game
     * @param name - name of current player
     */
    public abstract void notifyOfNewTurn(String name);

    /**
     * Starts the user interface
     */
    public abstract void runUI();

    /**
     * Display the game board onto the current ui
     * @param board
     */
    public abstract void displayBoard(String board);

    /**
     * Display messages incoming from the server and other game information
     * @param message - incoming message
     */
    public abstract void displayGameInfo(String message);

    /**
     * Displays the NEWGAME message and does any appropriate action
     * @param message
     */
    public abstract void notifyNewGame(String message);

    /**
     * Displayes the GAMEOVER message and does any appropriate action
     * @param message
     */
    public abstract void notifyGameOver(String message);

    /**
     * Asks the user for the address and port of the server they want to connect to
     */
    public abstract void askAddressandPort();
}
