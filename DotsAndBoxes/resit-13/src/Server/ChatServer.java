package src.Server;

import java.io.IOException;
import java.net.Socket;
import java.util.*;
import src.game.DotsAndBoxesMove;

/**
 * The class extends SocketServer and represents the server of the game
 */
public class ChatServer extends SocketServer {

    private Set<ClientHandler> clients;

    private Set<String> clientNames;

    private Set<ClientHandler> clientHandlerNames;

    private Queue<ClientHandler> queue = new LinkedList<>();

    private static String description = "DotsAndBoxesServer";

    private Map<ClientHandler, GameServer> clientHandlerGameServerMap = new HashMap<>();

    /**
     * Constructs a new ChatServer
     * @param port the port to listen on
     * @throws IOException if the server socket cannot be created, for example, because the port is already bound.
     */
    public ChatServer(int port) throws IOException {
        super(port);
        clients = new HashSet<>();
        clientNames = new HashSet<>();
        clientHandlerNames = new HashSet<>();
    }

    /**
     * The method adds a client to the queue after the client sends a QUEUE message
     * @param clientHandler is the client
     */
    public synchronized void addClientToQueue(ClientHandler clientHandler) {
        queue.add(clientHandler);
    }

    public synchronized void removeClientFromQueue(ClientHandler clientHandler) {
        getQueue().remove(clientHandler);
    }

    /**
     * This method returns the queue containing the clients
     * @return queue
     */
    public Queue<ClientHandler> getQueue() {
        return queue;
    }

    /**
     * The method checks is the queue has enough clients and then takes the first two clients waiting in the queue
     * and invokes the createGameServer method using them as arguments
     * @return list of two clients
     */
    public synchronized List<ClientHandler> getFirstTwoElements() {
        ClientHandler c1 = null;
        ClientHandler c2 = null;
        //Removes first two players from queue if it is not empty and creates a new game
        if (!queue.isEmpty()) {
            c1 = queue.poll();
        }
        if (!queue.isEmpty() && !queue.contains(c1)) {
        c2 = queue.poll();
        }
        if(c1 != null && c2 != null) {
            createGameServer(c1, c2);

            List<ClientHandler> two = new ArrayList<>();
            two.add(c1);
            two.add(c2);
            return two;
        }
        if(c1 != null){
            queue.add(c1);
        }
        if(c2 != null){
            queue.add(c2);
        }
        System.out.println("Stoped from having null clients");
        return null;
    }

    /**
     * This method uses the two clients provided as arguments in order to create a game server where the game is played
     * @param clientHandler1 is one client
     * @param clientHandler2 is another client
     * @return GameServer
     */
    //@requires clientHandler1 != null && clientHandler2 != null;
    public GameServer createGameServer(ClientHandler clientHandler1, ClientHandler clientHandler2) {
        GameServer gameServer = new GameServer(clientHandler1, clientHandler2);
        clientHandler1.setInGame(true);
        clientHandler2.setInGame(true);
        clientHandler1.setCurrentGame(gameServer);
        clientHandler2.setCurrentGame(gameServer);
        clientHandlerGameServerMap.put(clientHandler1, gameServer);
        clientHandlerGameServerMap.put(clientHandler2, gameServer);
        return gameServer;
    }

    /**
     * Adds the client after it has been logged in
     * @param clientHandler is the client
     */
    public void addClientHandlerAfterLogin(ClientHandler clientHandler) {
        clientHandlerNames.add(clientHandler);
    }

    /**
     * This returns the set of names of clients
     * @return set of names
     */
    public Set<String> getClientNames() {
        return clientNames;
    }

    /**
     * Returns the port on which this server is listening for connections.
     *
     * @return the port on which this server is listening for connections
     */
    @Override
    public int getPort() {
        return super.getPort();
    }

    /**
     * Accepts connections and starts a new thread for each connection.
     * This method will block until the server socket is closed, for example by invoking closeServerSocket.
     *
     * @throws IOException if an I/O error occurs when waiting for a connection
     */
    @Override
    public void acceptConnections() throws IOException {
        super.acceptConnections();
    }

    /**
     * Closes the server socket. This will cause the server to stop accepting new connections.
     * If called from a different thread than the one running acceptConnections, then that thread will return from
     * acceptConnections.
     */
    @Override
    public synchronized void close() {
        super.close();
    }

    /**
     * Creates a new connection handler for the given socket.
     *
     * @param socket the socket for the connection
     * @return the connection handler
     */
    @Override
    protected void handleConnection(Socket socket) {
        try {
            ServerConnection serverConnection = new ServerConnection(socket);
            ClientHandler clientHandler = new ClientHandler(this, serverConnection);
            serverConnection.setClientHandler(clientHandler);
            serverConnection.start();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * Adds a client to the HashSet of clients
     * @param client represents the client
     */
    //@requires client != null;
    //@ensures clients.contains(client);
    public synchronized void addClient(ClientHandler client) {
        clients.add(client);
        System.out.println("New client connected");
    }

    /**
     * The method adds the name of the client to the set of client names
     * @param name is name
     */
    //@requires name != null;
    //@ensures getClientNames().contains(name);
    public synchronized void addClientLogin(String name) {
        clientNames.add(name);
    }

    /**
     * Removes client from the HashSet of clients
     * @param client represents the client
     */
    //@requires client != null;
    //@ensures !clients.contains(client);
    public synchronized void removeClient(ClientHandler client) {
        clients.remove(client);
        clientHandlerNames.remove(client);
        clientNames.remove(client.getName());
        System.out.println("Client disconnected");
    }

    /**
     * The method returns the given description of the server
     * @return description
     */
    //@pure
    public String getDescription() {
        return description;
    }

    /**
     * The method returns false if another user that has logged in has the same username and sends an alreadyloggenin message
     * @param name is name of client
     * @param clientHandler is the client
     * @return false if username exists
     */
    public boolean checkUsername(String name, ClientHandler clientHandler) {
        if (clientNames.isEmpty()) {
            return true;
        }
        for (ClientHandler c : clientHandlerNames) {
            if (c.getName().equals(name)) {
                clientHandler.sendAlreadyLoggedIn();
                return false;
            }
        }
        return true;
    }

    /**
     * This method gets the game server using the client as an argument and then instructs the game server to
     * use its own doMove method using the index from the move as an argument
     * @param move is the move
     * @param clientHandler is the client
     */
    public synchronized void doMove(DotsAndBoxesMove move, ClientHandler clientHandler) {
        GameServer gameServer = clientHandlerGameServerMap.getOrDefault(clientHandler, null);
        ClientHandler c;

        if (gameServer == null) {
            clients.remove(clientHandler);
            clientHandlerNames.remove(clientHandler);
            clientNames.remove(clientHandler.getName());
            clientHandler.sendGeneral(Protocol.DISCONNECT);
            System.out.println("No game server");

        }
        int idx = move.getIdx();
        gameServer.doMove(idx, clientHandler);
    }

    public static void main(String[] args) {
        Scanner input = new Scanner(System.in);
        System.out.println("Enter a port number");
        int port = input.nextInt();
        input.nextLine();
        while (port < 0 || port > 65536) {
            System.out.println("Invalid port. Enter a port number");
            port = input.nextInt();
            input.nextLine();
        }
        try {
            ChatServer chatServer = new ChatServer(port);
            int actualPort = chatServer.getPort();
            System.out.println("Server started at port " + actualPort);
            chatServer.acceptConnections();
        }
        catch (IOException io) {
            io.printStackTrace();
        }
    }
}
