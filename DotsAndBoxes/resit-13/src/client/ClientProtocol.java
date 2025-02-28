package src.client;

import src.game.DotsAndBoxesMove;

import java.util.List;
import java.util.concurrent.locks.ReentrantLock;

/**
 * Class used to handle incoming and outgoing messages, format them to fit the given protocol and perform certain actions.
 */
public class ClientProtocol {

    public static final String HELLO = "HELLO";
    public static final String LIST = "LIST";
    public static final String HINT = "HINT";
    public static final String HELP = "HELP";
    public static final String LOGIN = "LOGIN";
    public static final String QUEUE = "QUEUE";
    public static final String MOVE = "MOVE";
    public static final String SEPARATOR = "~";
    public static final String ALREADYLOGGEDIN = "ALREADYLOGGEDIN";
    public static final String NEWGAME = "NEWGAME";
    public static final String GAMEOVER = "GAMEOVER";
    private static boolean loggedIN = false;

    private boolean inQueue = false;
    private boolean inGame = false;
    private Client c;
    private boolean recievedResponse = false;
    private UI ui;

    public ClientProtocol(Client client) {
        this.c = client;
        this.ui = client.getUi();
    }


    /**
     * Sent by a client to request a list of clients who are currently logged into the server.
     * Allowed at any point once the client is logged in, including during a game.
     * @return the formatted message that can be sent to the server
     */
    //@ ensures \result == "LIST";
    public static String sendList() {
        return LIST;
    }

    /**
     * Sent by the client to indicate that it wants to participate in a game.
     * The server will place the client at the back of the queue of waiting players.
     * When the command is issued a second time, the client is removed from the queue.
     * The server does not send a reply.
     * @return the formatted message that can be sent to the server
     */
    //@ ensures \result == "QUEUE";
    public static String sendQueue() {
        return QUEUE;
    }

    /**
     * Sent by the client to indicate which row(s) or column(s) the player wants to push.
     * Only allowed when it is the player's turn.
     * @param move - the move the user wishes to do (if it's valid hopefully)
     * @return the formatted message that can be sent to the server
     */
    //@ requires Integer.parseInt( move) >= 0 && Integer.parseInt( move) <= 59;
    //@ ensures \result == "MOVE~" + move;
    public static String sendMove(String move) {
        return MOVE + SEPARATOR + move;
    }

    /**
     * The initial message sent by the client once a connection has been established.
     * @param description - description of the things we have implemented
     * @return the formatted message that can be sent to the server
     */
    //@ requires description != null;
    //@ensures \result == "HELO~" + description;
    public static String sendHello(String description) {
        return HELLO + SEPARATOR + description;
    }

    /**
     * Sent by the client to claim a username on the server. When there is already a
     * client logged in with this username, the server should respond with
     * ALREADYLOGGEDIN, and the client should try a different username. Otherwise,
     * the server will respond with LOGIN.
     * @param name - username the user wants to claim
     * @return the formatted message that can be sent to the server
     */
    //@ requires name != null;
    //@ ensures \result == "LOGIN~" + name;
    public static String sendLogin(String name) {
        return LOGIN + SEPARATOR + name;
    }

    /**
     * Takes care of the incoming messages following their description in the protocol
     * @param incoming - the incoming message
     */
    //@ requires incoming != null;
    public synchronized void handleIncoming(String incoming) {

        String[] message = incoming.split("~");
        switch (message[0]){
            case LIST:
                ui.displayGameInfo(incoming);
                break;
            case LOGIN:
                loggedIN = true;
                this.notifyAll();
                ui.displayGameInfo(incoming);
                break;
            case QUEUE:
                inQueue = true;
                ui.displayGameInfo(incoming);
                break;
            case MOVE:
                this.notifyAll();
                ui.displayGameInfo(incoming);
                c.doMove(Integer.parseInt(message[1]));
                ui.notifyOfNewTurn(c.getTurn());
                break;
            case GAMEOVER:
                inGame = false;
                ui.notifyGameOver(incoming);
                inQueue = false;
                break;
            case HELLO:
                this.notifyAll();
                ui.displayGameInfo(incoming);
                break;
            case ALREADYLOGGEDIN:
                this.notifyAll();
                ui.displayGameInfo(incoming);
                break;
            case NEWGAME:
                this.notifyAll();
                inGame = true;
                c.createGame(message[1], message[2]);
                ui.notifyNewGame(incoming);
                break;


        }
    }

    /**
     * Takes care of the outgoing messages formating them and enacting any required action
     * @param incoming - the outgoing message
     * @return message formated according to protocol, ready to be sent
     */
    //@ requires incoming != null;
    //@ ensures \result == null || \result != null;
    public String handleOutgoing(String incoming){
        incoming = incoming.replace(" ", "~");
        String[] message = incoming.split("~");
        message[0] = message[0].toUpperCase();
        switch (message[0]){
            case LIST:
                return sendList();
            case QUEUE:
                if (!inQueue) {
                    return sendQueue();
                }else{
                    return null;
                }
            case MOVE:
                if (message.length > 1) {
                    return sendMove(message[1]);
                }else {
                    return null;
                }
            case HINT:
                if(inGame) {
                    StringBuilder validMoves = new StringBuilder();
                    List<DotsAndBoxesMove> moves = c.getGame().getValidMoves();
                    for (DotsAndBoxesMove m : moves) {
                        validMoves.append(m.getIdx()).append("~");
                    }
                    ui.displayGameInfo("VALIDMOVES~" + validMoves);
                }
                return null;
            case HELP:
                    ui.displayGameInfo("List of Commands:");
                    ui.displayGameInfo("LIST - returns a list of all the connected users");
                    ui.displayGameInfo("QUEUE - adds you to the waiting queue for a new game of dots and boxes");
                    ui.displayGameInfo("HINT - gives you a list of all valid moves");
                    ui.displayGameInfo("MOVE - execute a move in the game, " +
                            "this should be used as: 'move x' where x is the index of the move you want to do");
                    ui.displayGameInfo("HELP - returns a list of commands");
            default:
                return null;
        }
    }

    /**
     * Used for synchronization in waiting for an incoming message before performing an action
     */
    public synchronized void waitMessage(){
        try {
            this.wait();
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
    }

    /**
     * notifies all the waiting threads that a new message came in
     */
    public synchronized void notifyOfMessage(){
        this.notifyAll();
    }

    /**
     * Returns if the user is logged in or not
     * @return is logged in or isn't
     */
    //@ ensures \result == loggedIN;
    public boolean isLoggedIN() {
        return loggedIN;
    }
}
