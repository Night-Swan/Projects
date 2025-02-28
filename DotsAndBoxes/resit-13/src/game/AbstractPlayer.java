package src.game;


/**
 * A player of a src.game.
 */
public abstract class AbstractPlayer {
    private final String name;

    /**
     * Creates a new src.game.Player object.
     */
    /*@ requires name != null;
        ensures getName() == name;
    @*/
    public AbstractPlayer(String name) {
        this.name = name;
    }

    /**
     * Returns the name of the player.
     * @return the name of the player
     */
    public String getName() {
        return name;
    }

    /**
     * Determines the next move, if the src.game still has available moves.
     * @param game the current src.game
     * @return the player's choice
     */
    //@ requires !game.isGameover();
    //@ ensures game.isValidMove(\result);
    public DotsAndBoxesMove determineMove(DotsAndBoxesGame game){return null;};

    /**
     * Returns a representation of a player, i.e., their name
     * @return the String representation of this object
     */
    @Override
    public String toString() {
        return name;
    }
}



