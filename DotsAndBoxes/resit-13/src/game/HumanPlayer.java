package src.game;

import java.io.InputStreamReader;
import java.util.List;
import java.util.Scanner;

/**
 * An extension to AbstractPlayer that allows for user input
 */
public class HumanPlayer extends AbstractPlayer {

    public HumanPlayer(String name) {
        super(name);
    }

    /**
     * Method used for receiving a move from the player
     * @param game the current src.game
     * @return the Move given by the player
     */
    public DotsAndBoxesMove determineMove(DotsAndBoxesGame game) {
        List<DotsAndBoxesMove> list = game.getValidMoves();
        DotsAndBoxesMove move;
        Scanner input = new Scanner(System.in);
        DotsAndBoxesGame newGame = (DotsAndBoxesGame) game;


        if (list.size() > 0) {
            System.out.println("Available moves: " + list);
            System.out.println("Give move index for " + this.getName());
            int index = input.nextInt();

            if (index >= 0 && index <= 59) {
                while (!newGame.isValidMove(new DotsAndBoxesMove(index))) {
                    System.out.println("Invalid index. Please enter a valid move index:");
                    index = input.nextInt();
                }
                move = new DotsAndBoxesMove(index);
                return move;
            } else {
                System.out.println("Index should be an integer between 0 and 59");
                return null;
            }
        } else {
            System.out.println("No available moves.");
            return null;
        }
    }
}
