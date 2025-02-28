package src.Server;

import java.net.ServerSocket;
import java.util.Set;
import src.game.DotsAndBoxesMove;

/**
 * Sends and receives messages to and from the client
 */
public class ClientHandler {

    private final ChatServer chatServer;
    private final ServerConnection serverConnection;

    private String name;

    private ServerState serverState;
    private GameServer currentGame;
    private boolean inGame;

    public ClientHandler(ChatServer chatServer, ServerConnection serverConnection) {
        this.chatServer = chatServer;
        this.serverConnection = serverConnection;
        serverConnection.setClientHandler(this);
        chatServer.addClient(this);
        this.serverState = ServerState.BEFORE_HELLO;
    }


    /**
     * Returns the name of the client
     * @return name
     */
    public String getName() {
        return name;
    }

    /**
     * This method is used to set name for the client
     * @param userName is the client name
     */
    public void setName(String userName) {
        this.name = userName;
    }

    /**
     * Sets the state of the server after a relevant action has been completed
     * @param serverState represents state of server
     */
    public void setServerState(ServerState serverState) {
        this.serverState = serverState;
    }

    /**
     * Returns the server that the client is connected with
     * @return server
     */
    public ChatServer getChatServer() {
        return chatServer;
    }

    /**
     * This method is called to change the state of the conneciton after HELLO message has been received and to
     * send a message back to the client
     */
    public void receiveHello() {
        if (this.serverState == ServerState.BEFORE_HELLO) {
            this.serverState = ServerState.RECEIVED_HELLO;
            sendHello();
        }
    }

    /**
     * The method first checks if the connection is in the proper state and then receives the login credentials from the
     * user and sends a message vck to the client
     */
    public void receiveLogin() {
        if (this.serverState == ServerState.RECEIVED_HELLO) {
            this.serverState = ServerState.RECEIVED_LOGIN;
            sendLogin();
        }
    }

    /**
     * This uses the instance of chatserver to add the current client to the queue
     */
    public synchronized void receiveQueue() {
        if (this.serverState == ServerState.CONFIRMED_LOGIN) {
            chatServer.addClientToQueue(this);
        }
    }


    /**
     *
     * @param move is the move to be made
     */
    public void receiveMove(DotsAndBoxesMove move) {
        if (this.serverState == ServerState.CONFIRMED_LOGIN) {
            chatServer.doMove(move, this);
        }
        String s = Protocol.MOVE + Protocol.SEPARATOR + move.getIdx();
        //sendGeneral(s);
    }

    /**
     * Sends a messge to the clients when the game is over using the argument as the reason
     * @param reason is reason for gameover
     */
    public void sendGameOver(String reason) {
        String s = Protocol.GAMEOVER + Protocol.SEPARATOR + reason;
        sendGeneral(s);
    }

    /**
     * The method is used to send the move being made to both clients in the game
     * @param move is the move
     */
    public void broadcastMove(DotsAndBoxesMove move) {
        String s = Protocol.MOVE + Protocol.SEPARATOR + move.getIdx();
        sendGeneral(s);
    }

    /**
     * This method is used when two clients are in the queue and then a message is sent to both clients that a new
     * game is formed consisting of both these clients
     * @param c1 is a client
     * @param c2 is another client
     */
    public void sendNewGameMessage(ClientHandler c1, ClientHandler c2) {
        String s = Protocol.NEWGAME + Protocol.SEPARATOR + c1.getName() + Protocol.SEPARATOR + c2.getName();
        sendGeneral(s);
    }

    /**
     * Used to send messages to the client with the instance of the serverconnection
     * @param command is the message being sent
     */
    public void sendGeneral(String command) {
        serverConnection.sendMessage(command);
    }

    /**
     * This method sends a response message consisting of the servers description when a client sends a HELLO message
     */
    public void sendHello() {
        String s = Protocol.HELLO + Protocol.SEPARATOR + chatServer.getDescription();
        sendGeneral(s);
    }

    /**
     * This method gets invoked when a client with the given name is already logged in and hence sends he appropriate message
     */
    public void sendAlreadyLoggedIn() {
        String s = Protocol.ALREADYLOGGEDIN;
        sendGeneral(s);
    }

    /**
     * This method sends a LOGIN message to a client that has logged in with a unique username
     */
    public void sendLogin() {
        String s = Protocol.LOGIN;
        sendGeneral(s);
    }

    /**
     * This method is used to send the list of current clients that have logged in when it receives a LIST message from a client
     * @param names is the list of names
     */
    public void receiveList(Set<String> names) {
        String res = "";
        for (String name : names) {
            res += Protocol.SEPARATOR + name;
        }
        String s = Protocol.LIST+res;
        sendGeneral(s);
    }

    /**
     * Sets the name of the client and adds the client to a set of clients in the chatserver
     * @param name is the name of the user
     */
    public void setUserName(String name) {
        this.name = name;
        chatServer.addClientLogin(name);
        chatServer.addClientHandlerAfterLogin(this);
    }

    public void setInGame(boolean inGame) {
        this.inGame = inGame;
    }

    public boolean isInGame() {
        return inGame;
    }

    /**
     * It uses the checkUsername method from the chatserver to check if the client with the name is logged in
     * @param name is the name of the client
     * @param clientHandler is the client
     * @return false if username exists
     */
    public boolean checkName(String name, ClientHandler clientHandler) {
        return chatServer.checkUsername(name, clientHandler);
    }

    /**
     * Sets the game server for the current client
     * @param currentGame is the gameserver
     */
    public void setCurrentGame(GameServer currentGame) {
        this.currentGame = currentGame;
    }

    /**
     * The method returns the game server that is used by the client
     * @return the game server
     */
    public GameServer getCurrentGame() {
        return currentGame;
    }
}
