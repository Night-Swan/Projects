package test;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import src.game.*;

import static org.junit.jupiter.api.Assertions.*;
import static org.junit.jupiter.api.Assertions.assertEquals;

public class GameTests {
    private Board board;
    private DotsAndBoxesGame game;
    private AbstractPlayer player1, player2;


    /**
     * Set up for the tests
     */
    @BeforeEach
    public void setUp(){
        this.board = new Board();
        HumanPlayer player2, player1;
        player1 = new HumanPlayer("Somone");
        player2 = new HumanPlayer("Jorge");
        this.player1 = player1;
        this.player2 = player2;
        this.game = new DotsAndBoxesGame(player1, player2);
    }

    /**
     * Test if a player has been properly created by getting their name
     */
    @Test
    public void playerCreationTest(){
        AbstractPlayer p1 = new AbstractPlayer("K2SO") {};
        assertEquals(player1.getName(), "Somone");
        assertEquals(player2.toString(), "Jorge");
        assertNull(p1.determineMove(game));
    }

    /**
     * Test if a move is created properly
     */
    @Test
    public void createMoveTest(){
        DotsAndBoxesMove move = new DotsAndBoxesMove(1);
        assertEquals("Index 1", move.toString());
    }

    /**
     * Test if a game ends when the board is filled
     */
    @Test
    public void isGameOverTest(){
        for (int i=0; i<=59; i++){
            assertFalse(board.isGameOver());
            board.setField(i);
        }
        assertTrue(board.isGameOver());
    }

    /**
     * Test if moves are executed correctly on the board
     */
    @Test
    public void moveTest(){
        DotsAndBoxesMove move = new DotsAndBoxesMove(6);
        this.game.doMove(move);
        assertEquals(Board.Mark.VERTICAL_LINE, game.getBoard().getField(6));
        move = new DotsAndBoxesMove(0);
        this.game.doMove(move);
        assertEquals(Board.Mark.HORIZONTAL_LINE, game.getBoard().getField(0));
    }

    /**
     * Test if the winner is returned correctly
     */
    @Test
    public void findWinnerTest (){
        for(int i = 0; i <= 59; i++){
            assertFalse(game.isGameover());
            DotsAndBoxesMove move = new DotsAndBoxesMove(i);
            this.game.doMove(move);
            System.out.println(this.game.getBoard().toString());
        }

        assertEquals(game.getWinner(), player2);
    }

    /**
     * Test if the score updates correctly when a box is closed
     */
    @Test
    public void scoreUpdateTest(){
        doMove(0);
        doMove(5);
        doMove(6);
        doMove(2);
        doMove(7);
        doMove(8);
        doMove(19);
        doMove(18);
        doMove(24);
        assertEquals(game.getPlayer2Score(), 0);
        doMove(11);
        assertEquals(game.getPlayer2Score(), 1);
        doMove(13);
        assertEquals(game.getPlayer2Score(), 3);
    }

    /**
     * Perform a move in the game of dots and boxes
     * @param index - the index of the move you want to do
     */
    private void doMove(int index) {
        DotsAndBoxesMove move;
        move = new DotsAndBoxesMove(index);
        this.game.doMove(move);
    }

}
