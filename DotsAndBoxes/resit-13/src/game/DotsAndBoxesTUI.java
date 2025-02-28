package src.game;

import java.util.Scanner;

/**
 * A textual user interface for the game of dots and boxes
 */
public class DotsAndBoxesTUI {

    private DotsAndBoxesGame game;
    private AbstractPlayer player1, player2;


    public DotsAndBoxesTUI(AbstractPlayer player1, AbstractPlayer player2) {
        this.player1 = player1;
        this.player2 = player2;
        this.game = new DotsAndBoxesGame(player1, player2);
    }

    /**
     * Starts the TUI for a dots and boxes game
     */
    public void run() {
        if (game.isGameover()) {
            System.out.println("Game Over");
        }
        while (!game.isGameover()) {
            DotsAndBoxesMove move;
            Scanner x = new Scanner(System.in);
            Board board = game.getBoard();
            System.out.println("Player 1 Score: " + game.getPlayer1Score());
            System.out.println("Player 2 Score: " + game.getPlayer2Score());
            System.out.println(board.toString());
            System.out.println("Which index do you want to add a line to " + game.getTurn() + ": ");
            int idx = x.nextInt();
            move = new DotsAndBoxesMove(idx);
            AbstractPlayer playerTurn = game.getTurn();
//            if (playerTurn instanceof src.game.HumanPlayer) {
//                System.out.println("Game Not Over");
//                System.out.println(src.game.getBoard().toString());
//                move = ((src.game.HumanPlayer) playerTurn).determineMove(this.src.game);
//            }
            this.game.doMove(move);
//            board = game.getBoard();
//            System.out.println("1 test");
//            System.out.println(board.toString());
//            System.out.println("2 test");


            if (game.isGameover()) {
                System.out.println("GAME OVER");
                System.out.println(game.getBoard().toString());
                if (game.getWinner() != null) {
                    if (game.getWinner() instanceof HumanPlayer)
                        System.out.println(((HumanPlayer) (game.getWinner())).getName() + " is the winner");
                    System.out.println("Another src.game?  yes/ no");
                    Scanner input = new Scanner(System.in);
                    String word = input.nextLine();
                    if (word.equals("yes")) {
                        game = new DotsAndBoxesGame(player1, player2);
                    }
                } else System.out.println("It's a Tie");
            }
        }
    }

    public static void main(String[] args) {
        HumanPlayer player2, player1;
        Scanner input = new Scanner(System.in);

        System.out.println("Player1 name: ");
        String name1 = input.nextLine();
        player1 = new HumanPlayer(name1);


        System.out.println("Player2 name: ");
        String name2 = input.nextLine();
        player2 = new HumanPlayer(name2);

        DotsAndBoxesTUI tui = new DotsAndBoxesTUI(player1, player2);
        tui.run();
    }
}

