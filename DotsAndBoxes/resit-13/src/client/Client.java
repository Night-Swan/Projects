package src.client;

import src.game.AbstractPlayer;
import src.game.DotsAndBoxesGame;
import src.game.DotsAndBoxesMove;

import java.io.IOException;
import java.net.InetAddress;
import java.util.ArrayList;
import java.util.List;

/**
 * Main bulk of the client, this acts as a bridge between the ui and the client connection
 */
public class Client {

    private static final String address = "localhost";
//    private static final String address = "130.89.253.64";
    private String username;
    private static final int port = 4567;
    private ClientProtocol protocol;
    private DotsAndBoxesGame game;
    private UI ui;
    private List<Listener> listenerList = new ArrayList<>();
    private final InetAddress ServerAddress = InetAddress.getByName(address);;

    private ClientConnection cc;

    public Client(UI ui) throws IOException {
        this.ui = ui;
        this.protocol = new ClientProtocol(this);
        this.cc = new ClientConnection(ServerAddress, port, protocol);
        this.listenerList.add(this.cc.startGameListener());
    }

    public Client(UI ui, InetAddress address, int port) throws IOException {
        this.ui = ui;
        this.protocol = new ClientProtocol(this);
        this.cc = new ClientConnection(address, port, protocol);
        this.listenerList.add(this.cc.startGameListener());
    }

    /**
     * Sends a loggIn message to the server
     * @param userName - the username the user wishes to logg in with
     * @return - true/false if the message has been sent or not
     */
    //@ requires userName != null;
    //@ ensures cc.sendData(ClientProtocol.sendLogin(userName));
    public boolean sendLogin(String userName){
        return(cc.sendData(ClientProtocol.sendLogin(userName)));
    }

    /**
     * Sends a message to the server, after performing the correct protocol modifications
     * @param message - message to be sent
     * @return - true/false if the message has been sent or not
     */
    //@ requires message != null;
    //@ ensures \result == (protocol.handleOutgoing(message) != null && cc.sendData(protocol.handleOutgoing(message)));
    public boolean sendMessage(String message){
        String send = protocol.handleOutgoing(message);
//        System.out.println(send);
        if (send != null) {
            return (cc.sendData(send));
        }else {
            return false;
        }
    }

    /**
     * Memorizes the name the user has logged in with
     * @param username - the username the user logged in with
     */
    //@ requires username != null;
    //@ ensures this.username.equals(username);
    public void setUsername(String username) {
        this.username = username;
    }

    /**
     * Get the username the user logged in with
     * @return - the name of the current user
     */
    //@ ensures \result == this.username;
    public String getUsername() {
        return username;
    }

    /**
     * Check if user is logged in
     * @return - is logged in or isn't (boolean)
     */
    //@ ensures \result == protocol.isLoggedIN();
    public boolean checkLoggedIn(){
        return protocol.isLoggedIN();
    }

    /**
     * returns the protocol beeing used to handle incoming and outgoing messages;
     * @return - current protocol
     */
    //@ ensures \result == this.protocol;
    public ClientProtocol getProtocol(){
        return protocol;
    }

    /**
     * Creates a game between two people
     * @param p1 - the name of the first player to be put in the game
     * @param p2 - the name of the second player to be put in the game
     */
    //@ requires p1 != null && p2 != null;
    //@ ensures game != null && !game.isGameover();
    public void createGame(String p1, String p2){
        AbstractPlayer player1, player2;
        player1 = new AbstractPlayer(p1) {};
        player2 = new AbstractPlayer(p2) {};
        game = new DotsAndBoxesGame(player1, player2);
        ui.displayGameInfo("Player 1 score: " + game.getPlayer1Score());
        ui.displayGameInfo("Player 2 score: " + game.getPlayer2Score());
        ui.displayBoard(game.getBoard().toString());
        ui.notifyOfNewTurn(game.getTurn().getName());
    }

    /**
     * Perform the move in the game of dots and boxes
     * @param index - the move that has to be performed
     */
    //@ requires game != null;
    //@ requires 0 <= index && index <= 59;
    public void doMove(int index){
        DotsAndBoxesMove move = new DotsAndBoxesMove(index);
        game.doMove(move);
        ui.displayGameInfo("Player 1 score: " + game.getPlayer1Score());
        ui.displayGameInfo("Player 2 score: " + game.getPlayer2Score());
        ui.displayBoard(game.getBoard().toString());
    }

    /**
     * returns the name of the player who has the current turn
     * @return - the name of the current player
     */
    //@ requires game != null;
    //@ ensures \result.equals(game.getTurn().getName());
    public String getTurn(){
        return game.getTurn().getName();
    }

    /**
     * returns the ui that has created the client
     * @return - ui that is being used
     */
    //@ ensures \result == ui;
    public UI getUi() {
        return ui;
    }

    /**
     * Gets the current game of dots and boxes
     * @return - current game
     */
    //@ ensures \result == game;
    public DotsAndBoxesGame getGame(){
        return game;
    }
}
