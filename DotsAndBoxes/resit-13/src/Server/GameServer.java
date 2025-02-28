package src.Server;

import src.game.AbstractPlayer;
import src.game.Board;
import src.game.DotsAndBoxesGame;
import src.game.DotsAndBoxesMove;

import java.util.Objects;

/**
 * Game created by the server from two clients in the queue
 */
public class GameServer {

    private DotsAndBoxesGame game;

    private AbstractPlayer playerServer1;

    private AbstractPlayer playerServer2;

    private ClientHandler currentClient;

    private AbstractPlayer currentPlayer;



    public GameServer(ClientHandler clientHandler1, ClientHandler clientHandler2) {
        this.clientHandler1 = clientHandler1;
        this.clientHandler2 = clientHandler2;
        playerServer1 = new AbstractPlayer(clientHandler1.getName()) { };
        playerServer2 = new AbstractPlayer(clientHandler2.getName()) { };
        game = new DotsAndBoxesGame(playerServer1, playerServer2);
        currentPlayer = playerServer1;
        currentClient = clientHandler1;
    }

    private ClientHandler clientHandler1;

    private ClientHandler clientHandler2;


    /**
     * This method allows the client to make a move
     * @param index is the index
     * @param client is the ClientHandler
     */
    public void doMove(int index, ClientHandler client) {
        //To make sure the client can play the game only when it is their turn
            if (game.getCurrentPlayer().getName().equals(client.getName())) {
                if (isValidMove(index)) {
                    DotsAndBoxesMove move = new DotsAndBoxesMove(index);
                    game.doMove(move);

                    clientHandler1.broadcastMove(move);
                    clientHandler2.broadcastMove(move);

                    if (!game.scoreChanged()) {
                        if (currentClient.equals(clientHandler1)) {
                            currentClient = clientHandler2;
                            currentPlayer = playerServer2;
                        }
                        else {
                            currentClient = clientHandler1;
                            currentPlayer = playerServer1;
                        }
                    }

                    if (isGameOver()) {
                        clientHandler1.setInGame(false);
                        clientHandler2.setInGame(false);
                        clientHandler1.setCurrentGame(null);
                        clientHandler2.setCurrentGame(null);
                        if (game.getWinner() != null) {
                            if (clientHandler1.getName().equals(game.getWinner())) {
                                clientHandler1.sendGameOver(Protocol.VICTORY + Protocol.SEPARATOR + clientHandler1.getName());
                                clientHandler2.sendGameOver(Protocol.VICTORY + Protocol.SEPARATOR + clientHandler1.getName());
                            }
                            else {
                                clientHandler1.sendGameOver(Protocol.VICTORY + Protocol.SEPARATOR + clientHandler2.getName());
                                clientHandler2.sendGameOver(Protocol.VICTORY + Protocol.SEPARATOR + clientHandler2.getName());
                            }
                        }
                        else {
                            clientHandler1.sendGameOver(Protocol.DRAW);
                            clientHandler2.sendGameOver(Protocol.DRAW);
                        }
                    }
                }
            }


    }

    /**
     * Gets invoked when one of the players gets disconnected from the game and then prints the appropriate message
     * @param disconnected is the ClientHandler
     */
    public void endPrematruley (ClientHandler disconnected){
        clientHandler1.setInGame(false);
        clientHandler2.setInGame(false);
        clientHandler1.setCurrentGame(null);
        clientHandler2.setCurrentGame(null);
        if (Objects.equals(disconnected.getName(), clientHandler1.getName())){
            clientHandler1.sendGameOver(Protocol.DISCONNECT + Protocol.SEPARATOR + clientHandler2.getName());
            clientHandler2.sendGameOver(Protocol.DISCONNECT + Protocol.SEPARATOR + clientHandler2.getName());
        }else if (Objects.equals(disconnected.getName(), clientHandler2.getName())){
            clientHandler1.sendGameOver(Protocol.DISCONNECT + Protocol.SEPARATOR + clientHandler1.getName());
            clientHandler2.sendGameOver(Protocol.DISCONNECT + Protocol.SEPARATOR + clientHandler1.getName());
        }else {
            clientHandler1.sendGameOver(Protocol.DRAW);
            clientHandler2.sendGameOver(Protocol.DRAW);
        }
    }

    /**
     * Checks if the index given in the argument represents a valid move on the board
     * @param idx is index
     * @return true if move is valid
     */
    public boolean isValidMove(int idx) {
        if (idx <= 59 && idx >= 0 && (getGame().getBoard().getField(idx) == Board.Mark.EMPTY || getGame().getBoard().getField(idx) == null)) {
            return true;
        }
        return false;
    }

    /**
     * Checks if the instance of game has finished by using the isGameOver method from DotsAndBoxesGame class
     * @return true if game is over
     */
    public boolean isGameOver() {
        return game.isGameover();
    }

    /**
     * The method returns the current DotsAndBoxes game between the two clients
     * @return game
     */
    public DotsAndBoxesGame getGame() {
        return game;
    }

}
