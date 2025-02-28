package src.AI;

import src.game.AbstractPlayer;
import src.game.Board;
import src.game.DotsAndBoxesGame;
import src.game.DotsAndBoxesMove;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

public class SmartAI extends AbstractPlayer {
    /**
     * Creates a new src.game.Player object.
     *
     * @param name
     */
    //@ requires name != null;
    //@ ensures getName().equals(name);
    public SmartAI(String name) {
        super(name);
    }


    /**
     * Finds moves that will close boxes
     * @param game - the current Game object that is being played
     * @return a list of all the moves that would close boxes
     */
    //@ requires game != null;
    //@ ensures \result != null;
    //@ pure
    public List<DotsAndBoxesMove> winingMoves(DotsAndBoxesGame game){
        List<DotsAndBoxesMove> goodMoves = new ArrayList<>();
        List<DotsAndBoxesMove> badMoves = new ArrayList<>();
        List<DotsAndBoxesMove> validMoves = game.getValidMoves();
        for (DotsAndBoxesMove d : validMoves) {
            Board copyBoard = game.getBoard().deepCopy();
            copyBoard.setField(d.getIdx());
            for (DotsAndBoxesMove m : validMoves){
                Board copyCopyBoard = copyBoard.deepCopy();
                copyCopyBoard.setField(m.getIdx());
                if (copyBoard.numSquares() > copyBoard.getTotalSquares()) {
                    badMoves.add(d);
                }
            }
            if (copyBoard.numSquares() > copyBoard.getTotalSquares()) {
                goodMoves.add(d);
            }
        }
        return goodMoves;
    }

    /**
     * Finds moves that will allow the opponent to close boxes
     * @param game - current src.game
     * @return a list of bad moves
     */
    //@ requires game != null;
    //@ ensures \result != null;
    //@ pure
    public List<DotsAndBoxesMove> loosingMoves(DotsAndBoxesGame game){
        List<DotsAndBoxesMove> goodMoves = new ArrayList<>();
        List<DotsAndBoxesMove> badMoves = new ArrayList<>();
        List<DotsAndBoxesMove> validMoves = game.getValidMoves();
        for (DotsAndBoxesMove d : validMoves) {
            Board copyBoard = game.getBoard().deepCopy();
            copyBoard.setField(d.getIdx());
            for (DotsAndBoxesMove m : validMoves){
                Board copyCopyBoard = copyBoard.deepCopy();
                copyCopyBoard.setField(m.getIdx());
                if (copyBoard.numSquares() > copyBoard.getTotalSquares()) {
                    badMoves.add(d);
                }
            }
            if (copyBoard.numSquares() > copyBoard.getTotalSquares()) {
                goodMoves.add(d);
            }
        }
        return badMoves;
    }
    /**
     * Determines a move by making sure the opponent will not finish boxes while also doing moves that will finish boxes
     * @param game the current src.game
     * @return a move that is beyond human comprehension
     */
    //@ requires game != null;
    //@ ensures \result != null;
    //@ pure
    public DotsAndBoxesMove determineMove(DotsAndBoxesGame game) {
        List<DotsAndBoxesMove> validMoves = game.getValidMoves();
        List<DotsAndBoxesMove> goodMoves = winingMoves(game);
        List<DotsAndBoxesMove> badMoves = loosingMoves(game);
        if (goodMoves.size() > 0){
            return goodMoves.get((new Random()).nextInt(goodMoves.size()));
        }
        List<DotsAndBoxesMove> decentMoves = validMoves;
        validMoves.removeAll(badMoves);
        if(validMoves.size() > 0) {
            return validMoves.get((new Random()).nextInt(validMoves.size()));
        }else{
            return decentMoves.get((new Random()).nextInt(validMoves.size()));
        }
    }
}
