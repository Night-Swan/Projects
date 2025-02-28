package src.client;

import src.AI.DumbAI;
import src.AI.NormalAI;
import src.AI.SmartAI;
import src.game.AbstractPlayer;
import src.game.DotsAndBoxesGame;
import src.game.DotsAndBoxesMove;

import java.io.IOException;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Objects;
import java.util.Random;
import java.util.Scanner;

public class AIUI extends UI{
    private Client client;
    private AbstractPlayer bot;
    private InetAddress address = InetAddress.getByName("LocalHost");
    private int port = 4567;

    //@ ensures this.address != null;
    public AIUI() throws UnknownHostException {
    }

    //@ ensures this.client != null;
    //@ requires this.address != null;
    //@ requires this.port >= 0;
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
//    public void startClient() throws IOException {
//        askAddressandPort();
//        this.client = new Client(this, this.address, this.port);
//    }
    /**
     * Prints out the name of the current player in the game
     * @param name - name of current player
     */
    //@ requires name != null;
    //@ ensures this.client.getGame().getTurn().getName().equals(client.getUsername()) ==> this.client.sendMessage("MOVE " + bot.determineMove(client.getGame()).getIdx());
    @Override
    public synchronized void notifyOfNewTurn(String name){
        System.out.println("It's " + name + "'s Turn");
        if (client.getGame().getTurn().getName().equals(client.getUsername()) && !client.getGame().isGameover()){
            int m = bot.determineMove(client.getGame()).getIdx();
            System.out.println(m);
            client.sendMessage("MOVE " + m);
        }
    }

    /**
     * Starts the user interface
     */
    //@ ensures this.bot != null;
    @Override
    public void runUI() {
        client.getProtocol().waitMessage();
        Scanner input = new Scanner(System.in);
            this.bot = createDifficulty(input);
            client.setUsername(bot.getName());
            client.sendLogin(bot.getName());
            this.AIActions();
            String message = input.nextLine();
            while(!message.startsWith("EXIT")){
                message = input.nextLine();
            }
    }

    //@ requires this.client != null;
    //@ ensures this.client.sendMessage("QUEUE");
    public void AIActions(){
                client.sendMessage("QUEUE");

    }

    /**
     * Allows the user to choose the difficulty of their bot
     * @param input - user input scanner
     * @return AbstractPlayer representing the bot with the difficulty of the users choice
     */
    //@ requires input != null;
    //@ ensures \result != null;
    public AbstractPlayer createDifficulty(Scanner input){
        System.out.println("Choose Difficulty: easy/normal/hard ");
        String difficulty = input.nextLine();
        if (difficulty.equalsIgnoreCase("easy")){
            return new DumbAI("#DotsAndBoxesDumbBot" + ((int)(Math.random() * 10000 + 1)));
        }else if (difficulty.equalsIgnoreCase("normal")){
            return new NormalAI("#DotsAndBoxesNormalBot" + ((int)(Math.random() * 10000 + 1)));
        }else if (difficulty.equalsIgnoreCase("hard")){
            return new SmartAI("#DotsAndBoxesSmartBot" + ((int)(Math.random() * 10000 + 1)));
        }else {
            System.out.println("Please provide a valid difficulty!");
            return(createDifficulty(input));
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
     */
    //@ requires message != null;
    //@ ensures this.client.sendMessage("QUEUE");
    @Override
    public void notifyGameOver(String message) {
        client.sendMessage("QUEUE");
        System.out.println(message);
    }

    /**
     * Asks the user for the address and port of the server they want to connect to
     */
    //@ ensures this.address != null;
    //@ ensures this.port > 0;
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


    public static void main(String[] args) throws IOException {
        AIUI aiui = new AIUI();
        aiui.startClient();
        aiui.runUI();
    }
}
