package src.Server;

import java.io.IOException;
import java.net.Socket;
import java.util.List;
import java.util.Set;
import src.game.DotsAndBoxesMove;

/**
 * The ServerConnection class handles the different messages sent by the client as well as handling disconnect
 */
public class ServerConnection extends SocketConnection{

    private ClientHandler clientHandler;

    public ServerConnection(Socket socket) throws IOException {
        super(socket);
    }

    /**
     * The method is used to handle the different types of messages being received from the client
     * It takes the first part of the message to differentiate the message into different types like HELLO, LOGIN etc
     * @param message the message received from the connection
     */
    public synchronized void handleMessage(String message) {
        String[] parts = message.split(Protocol.SEPARATOR);
        if (parts.length >= 1) {
            String init = parts[0];
            switch (init) {
                case Protocol.HELLO:
                    clientHandler.receiveHello();
                    break;
                case Protocol.LOGIN:
                    if (clientHandler.checkName(parts[1], clientHandler)) {
                        clientHandler.receiveLogin();
                        clientHandler.setUserName(parts[1]);
                        clientHandler.setServerState(ServerState.CONFIRMED_LOGIN);
//                        clientHandler.getChatServer().showClientHandlers();
                    }
                    break;
                case Protocol.LIST:
                    Set<String> names = clientHandler.getChatServer().getClientNames();
                    clientHandler.receiveList(names);
                    break;
                case Protocol.QUEUE:
                    clientHandler.receiveQueue();
                    if (clientHandler.getChatServer().getQueue().size() >= 2) {
                        List<ClientHandler> l =  clientHandler.getChatServer().getFirstTwoElements();
                        if (l != null) {
                            ClientHandler c1 = l.get(0);
                            ClientHandler c2 = l.get(1);
                            c1.sendNewGameMessage(c1, c2);
                            c2.sendNewGameMessage(c1, c2);
                        }
                    }
                    break;
                case Protocol.MOVE:
                    int index = Integer.parseInt(parts[1]);
                    DotsAndBoxesMove move = new DotsAndBoxesMove(index);
                    clientHandler.receiveMove(move);
                    break;
                default:
                    System.out.println("Invalid message");
                    break;
            }
        }
    }

    /**
     * Message printed on server console after client disconnects
     */
    @Override
    protected void handleDisconnect() {
        if (clientHandler.isInGame() && clientHandler.getCurrentGame() != null) {
            clientHandler.getCurrentGame().endPrematruley(clientHandler);
        }
        clientHandler.getChatServer().removeClient(clientHandler);
        clientHandler.getChatServer().removeClientFromQueue(clientHandler);
        System.out.println("Client disconnected");
    }

    /**
     * Adds a client handler for the connection
     * @param clientHandler is the client handler being added
     */
    public void setClientHandler(ClientHandler clientHandler) {
        this.clientHandler = clientHandler;
    }



}
