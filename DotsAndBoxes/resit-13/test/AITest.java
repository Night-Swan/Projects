package test;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import src.AI.DumbAI;
import src.AI.NormalAI;
import src.AI.SmartAI;
import src.game.AbstractPlayer;
import src.game.DotsAndBoxesGame;
import src.game.DotsAndBoxesMove;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

public class AITest {

    private DotsAndBoxesGame game;
    private DotsAndBoxesGame game2;
    private DotsAndBoxesGame game3;
    private AbstractPlayer player1, player2, player3, player4, player5, player6;

    /**
     * Set up for the tests
     */
    @BeforeEach
    public void setUp(){
        player1 = new DumbAI("Joey");
        player2 = new DumbAI("Mission");
        player3 = new NormalAI("Slime");
        player4 = new NormalAI("Juno");
        player5 = new SmartAI("Tali");
        player6 = new SmartAI("Peebee");

        this.game = new DotsAndBoxesGame(player1, player2);
        this.game2 = new DotsAndBoxesGame(player1, player3);
        this.game3 = new DotsAndBoxesGame(player4, player5);
    }

    /**
     * Test a game between two dumb AI (since we can not predict what moves will be performed there is no assert)
     */
    @Test
    public void  Dumb(){
        int t = 0;
//        this.game.doMove(new DotsAndBoxesMove(25));
        while(!game.isGameover()){
            t++;
//            assertFalse(game.isGameover());
            DotsAndBoxesMove move = this.game.getTurn().determineMove(this.game);
            this.game.doMove(move);
            System.out.println(move.getIdx());
            System.out.println(this.game.getBoard().toString());
        }
        System.out.println(t);
        System.out.println(this.game.getWinner());
    }

    /**
     * Test a game between a dumb AI and a normal AI (since we can not predict what moves will be performed there is no assert)
     */
    @Test
    public void Normal(){
        int t = 0;
//        this.game.doMove(new DotsAndBoxesMove(25));
        while(!game2.isGameover()){
            t++;
//            assertFalse(game.isGameover());
            DotsAndBoxesMove move = this.game2.getTurn().determineMove(this.game2);
            this.game2.doMove(move);
            System.out.println(move.getIdx());
            System.out.println(this.game2.getBoard().toString());
        }
        System.out.println(t);
        System.out.println(this.game2.getWinner());
    }

    /**
     * Test a game between a normal AI and a smart AI (since we can not predict what moves will be performed there is no assert)
     */
    @Test
    public void Smart(){
        int t = 0;
//        this.game.doMove(new DotsAndBoxesMove(25));
        while(!game3.isGameover()){
            t++;
//            assertFalse(game.isGameover());
            DotsAndBoxesMove move = this.game3.getTurn().determineMove(this.game3);
            this.game3.doMove(move);
            System.out.println(move.getIdx());
            System.out.println(this.game3.getBoard().toString());
        }
        System.out.println(t);
        System.out.println(this.game3.getWinner());
    }
}
