package src.AI;

import src.game.AbstractPlayer;
import src.game.Board;
import src.game.DotsAndBoxesGame;
import src.game.DotsAndBoxesMove;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

public class NormalAI extends AbstractPlayer {
    /**
     * Creates a new src.game.Player object.
     *
     * @param name
     */
    //@ requires name != null;
    //@ ensures getName().equals(name);
    public NormalAI(String name) {
        super(name);
    }

    /**
     * Finds moves that will close boxes
     * @param game the curent src.game
     * @return a list of moves that will close boxes
     */
    //@ requires game != null;
    //@ ensures \result != null;
    //@ pure
    public List<DotsAndBoxesMove> winingMoves(DotsAndBoxesGame game){
        List<DotsAndBoxesMove> goodMoves = new ArrayList<>();
        List<DotsAndBoxesMove> validMoves = game.getValidMoves();
        for (DotsAndBoxesMove d : validMoves) {
            Board copyBoard = game.getBoard().deepCopy();
            copyBoard.setField(d.getIdx());
//            System.out.println(copyBoard);
            if (copyBoard.numSquares() > copyBoard.getTotalSquares()) {
                goodMoves.add(d);
            }
        }
        return goodMoves;
    }

    /**
     * Determins a move my pure chance and by taking advantage of it's situation
     * @param game the current src.game
     * @return
     */
    //@ requires game != null;
    //@ ensures \result != null;
    //@ pure
    public DotsAndBoxesMove determineMove(DotsAndBoxesGame game) {
        List<DotsAndBoxesMove> validMoves = game.getValidMoves();
        List<DotsAndBoxesMove> goodMoves = winingMoves(game);
        if (goodMoves.size() > 0){
            return goodMoves.get((new Random()).nextInt(goodMoves.size()));
        }
        return validMoves.get((new Random()).nextInt(validMoves.size()));
    }
}
