package src.game;

/**
 * A move in the game of Dots and boxes
 */
public class DotsAndBoxesMove {
    private int idx;

    public DotsAndBoxesMove(int idx) {
        this.idx = idx;
    }

    /**
     * This method returns the index position on the board
     * @return index
     */
    public int getIdx() {
        return this.idx;
    }

    /**
     * The method returns the index position of the board in the form of string
     * @return index string
     */
    @Override
    public String toString() {
        return "Index " + idx;
    }
}
