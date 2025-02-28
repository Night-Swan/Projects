package src.client;

import java.io.IOException;
import java.net.ConnectException;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Objects;
import java.util.Scanner;

/**
 * A version of the ui that displays information in a textual user interface
 */
public class TUI extends UI{

    private Client client;
    private boolean loggedIn = false;

    private InetAddress address = InetAddress.getByName("LocalHost");
    private int port = 4567;

    public TUI() throws UnknownHostException {
    }

    /**
     * initializes the client and sends hello message to the server once connection is established
     * @throws IOException
     */
    public void startClient() throws UnknownHostException {
        askAddressandPort();
        try {
            this.client = new Client(this, this.address, this.port);
        } catch (IOException e) {
            System.out.println("Connection refused. Please input a valid address and port.");
            this.address = InetAddress.getByName("LocalHost");
            this.port = 4567;
            startClient();
        }
    }

    /**
     * Starts the user interface
     */
    //@ ensures loggedIn == true;
    @Override
    public synchronized void runUI() {
        client.getProtocol().waitMessage();
        Scanner input = new Scanner(System.in);
        System.out.println("Please avoid using the character ~");
//        client.getProtocol().waitMessage();
        do {
            System.out.println("Input Username: ");
            String userName = input.nextLine();
            if(userName.length() > 0) {
                if(!userName.contains("~")) {
                    client.setUsername(userName);
                    client.sendLogin(userName);
                    client.getProtocol().waitMessage();
                }else{
                    System.out.println("Invalid character used, please try again");
                }
            }else {
                System.out.println("Please enter a username");
            }

            loggedIn = client.checkLoggedIn();
//            System.out.println(loggedIn);
        }while(!loggedIn);
        System.out.println("\n \n \n");
        client.sendMessage("HELP");
        System.out.println("\n");
        String message = input.nextLine();
        while(!message.startsWith("EXIT")){
            client.sendMessage(message);
            message = input.nextLine();
        }
    }

    /**
     * Display the game board onto the current ui
     * @param board
     */
    //@ requires board != null;
    @Override
    public void displayBoard(String board) {
        System.out.println(board);
    }

    /**
     * Display messages incoming from the server and other game information
     * @param message - incoming message
     */
    //@ requires message != null;
    @Override
    public void displayGameInfo(String message) {
        System.out.println(message);
    }

    /**
     * Displays the NEWGAME message and does any appropriate action
     * @param message
     */
    //@ requires message != null;
    @Override
    public void notifyNewGame(String message) {
        System.out.println(message);
    }

    /**
     * Displayes the GAMEOVER message and does any appropriate action
     * @param message
     * //@ requires message != null;
     */
    @Override
    public void notifyGameOver(String message) {
        System.out.println(message);
        System.out.println("You can now join the queue again");
    }

    /**
     * Asks the user for the address and port of the server they want to connect to
     */
    //@ ensures address != null;
    //@ ensures port >= 0;
    @Override
    public void askAddressandPort() {
        Scanner input = new Scanner(System.in);
        boolean validInput = false;

        while (!validInput) {
            try {
                System.out.print("Input Server Address (Leave empty for LocalHost): ");
                String addressInput = input.nextLine();

                if (!addressInput.isEmpty()) {
                    this.address = InetAddress.getByName(addressInput);
                }

                System.out.print("Input Server Port (Leave empty for 4567): ");
                String portInput = input.nextLine();

                if (!portInput.isEmpty()) {
                    int port = Integer.parseInt(portInput);
                    if (port >= 0 && port <= 65535) {
                        this.port = port;
                        validInput = true;
                    } else {
                        throw new NotAPortException("Invalid port. Please enter a port within the range 0 to 65535.");
//                        System.out.println("Invalid port. Please enter a port within the range 0 to 65535.");
                    }
                } else {
                    validInput = true;
                }

            } catch (UnknownHostException | NumberFormatException e) {
                System.out.println("Invalid input. Please enter a valid address and port.");
            } catch (NotAPortException e) {
                System.out.println(e.getMessage());
            }
        }
    }

    /**
     * Prints out the name of the current player in the game
     * @param name - name of current player
     */
    //@ requires name != null;
    @Override
    public void notifyOfNewTurn(String name){
        System.out.println("It's " + name + "'s Turn");
    }
    public static void main(String[] args) throws IOException {
        TUI tui = new TUI();
        tui.startClient();
        tui.runUI();
    }
}
