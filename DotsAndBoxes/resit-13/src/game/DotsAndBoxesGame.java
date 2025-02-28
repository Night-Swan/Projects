package src.game;

import java.util.ArrayList;
import java.util.List;

/**
 * Class that represents a Dots and boxes game
 */
public class DotsAndBoxesGame {

    private Board board;
    private AbstractPlayer player1;
    private AbstractPlayer player2;
    private boolean isPlayer1;

    private int player1Score = 0;

    private int player2Score = 0;

    private AbstractPlayer currentPlayer;


    public DotsAndBoxesGame(AbstractPlayer player1, AbstractPlayer player2) {
        this.player1 = player1;
        this.player2 = player2;
        this.isPlayer1 = true;
        this.currentPlayer = player1;
        this.board = new Board();
    }

    /**
     * Uses the isGameOver method from the board field to check if the game is over
     * @return true if game is over
     */
    //@ensures \result == getBoard().isGameOver();
    //@pure
    public boolean isGameover() {
        return board.isGameOver();
    }

    /**
     * The method returns the player whose turn it is currently
     * @return current player
     */
    public AbstractPlayer getCurrentPlayer() {
        return currentPlayer;
    }

    /**
     * The method checks if there is a difference between the number of squares before and after a move has been made
     * @return true if score has changed
     */
    //@pure
    public boolean scoreChanged() {
        return board.getTotalSquares() != board.numSquares();
    }

    /**
     * This method checks if the move being made is valid by checking if the index is valid and there are no
     * other lines in that index
     * @param move is the move being made
     * @return true or false depending on move
     */
    //@requires move != null;
    //@ensures isGameover() ==> \result == false;
    //@ensures \result == (board.isField(move.getIdx()) && (board.getField(move.getIdx()) == Board.Mark.EMPTY || board.getField(move.getIdx()) == null));
    public boolean isValidMove(DotsAndBoxesMove move) {
        if (this.isGameover()) {
            return false;
        } else {
            if (move instanceof DotsAndBoxesMove) {
                int index = move.getIdx();
                if (board.isField(index) && (board.getField(index) == Board.Mark.EMPTY || board.getField(index) == null)) {
                    return true;
                }
            }
            return false;
        }
    }

    /**
     * The method sets a line on the given index after a move is made and then changes the scores of the
     * players if necessary
     * @param move is move being made
     */
    //@requires move != null;
    //@requires isValidMove(move);
    //@ensures board.getField(move.getIdx()) != null;
    public void doMove(DotsAndBoxesMove move) {
        if (isPlayer1) {
            currentPlayer = player1;
        }
        else {
            currentPlayer = player2;
        }
        if (this.isValidMove(move)) {
            int index = move.getIdx();
            board.setField(index);

            checkAddSquare();
        }
    }

    /**
     * The method returns a list of valid moves to choose from
     * @return list of moves
     */
    //@ensures (\forall DotsAndBoxesMove move; isValidMove(move); \result.contains(move));
    //@pure
    public List<DotsAndBoxesMove> getValidMoves() {
        List<DotsAndBoxesMove> moves = new ArrayList<>();
        for (int i = 0; i <= 59; i++) {
            if (board.isField(i) && board.getField(i) == Board.Mark.EMPTY) {
                DotsAndBoxesMove move = new DotsAndBoxesMove(i);
                moves.add(move);
            }
        }
        return moves;
    }

    /**
     * Gives the player name with the highest score
     * @return player
     */
    //@requires isGameover();
    //@ensures \result == null || (\result == player1 && player1Score > player2Score) || (\result == player2 && player2Score > player1Score);
    //@pure
    public AbstractPlayer getWinner() {

        if (isGameover()) {
            if (player1Score > player2Score) {
                return player1;
            }
            else if (player2Score > player1Score) {
                return player2;
            }
        }
        System.out.println("Tie");
        return null;
    }

    /**
     * This method returns the board in its current state
     * @return the board
     */
    //@pure
    public Board getBoard() {
        return this.board;
    }


    /**
     * Checks if the number of squares has been changed after a move has been made
     * If there is a change in the number of squares the score is increased for the player who made the move
     */
    //@ensures scoreChanged() ==> currentPlayer == \old(currentPlayer);
    public void checkAddSquare() {
        if (board.numSquares() > board.getTotalSquares()) {
            if (isPlayer1) {
                player1Score+= board.numSquares() - board.getTotalSquares();
                board.changeSquares(board.numSquares());
            }
            else {
                player2Score+= board.numSquares() - board.getTotalSquares();
                board.changeSquares(board.numSquares());
            }
        }
        else {
            if (isPlayer1) {
                isPlayer1 = false;
                currentPlayer = player2;
            }
            else {
                isPlayer1 = true;
                currentPlayer = player1;
            }
        }
    }

    /**
     * Gives the current player of the game whose turn it is to play
     * @return current player
     */
    //@pure
    public AbstractPlayer getTurn() {
        return currentPlayer;
    }

    /**
     * Method used to get the score of the first player
     * @return the score of player 1
     */

    //@pure
    public int getPlayer1Score() {
        return player1Score;
    }

    /**
     * Method used to get the score of the second player
     * @return the score of player 2
     */
    //@ensures \result == (\max int ; ; )
    //@pure
    public int getPlayer2Score() {
        return player2Score;
    }
}
