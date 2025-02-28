package src.game;

/**
 * The board of a dots and boxes game
 */
public class Board {
    public static final int DIM = 5;

    public enum Mark {
        EMPTY, DOT, HORIZONTAL_LINE, VERTICAL_LINE
    }

    public Mark[][] fields;


    private static String guideBoard = "*  00  *  01  *  02  *  03  *  04  *~" +
                          "05     06     07     08     09     10~" +
                          "*  11  *  12  *  13  *  14  *  15  *~" +
                          "16     17     18     19     20     21~" +
                          "*  22  *  23  *  24  *  25  *  26  *~" +
                          "27     28     29     30     31     32~" +
                          "*  33  *  34  *  35  *  36  *  37  *~" +
                          "38     39     40     41     42     43~" +
                          "*  44  *  45  *  46  *  47  *  48  *~" +
                          "49     50     51     52     53     54~" +
                          "*  55  *  56  *  57  *  58  *  59  *~" ;
    private String[] indexBoard  = guideBoard.split("~");


    private int totalSquares = 0;

    public Board() {
        fields = new Mark[DIM * 2 + 1][DIM * 2 + 1];
        initializeBoard();
    }


    /**
     * Sets the board with dots and empty spaces in their appropriate positions
     */
    private void initializeBoard() {
        for (int i = 0; i < DIM * 2 + 1; i++) {
            for (int j = 0; j < DIM * 2 + 1; j++) {
                if (i % 2 == 0 && j % 2 == 0) {
                    fields[i][j] = Mark.DOT;
                } else {
                    fields[i][j] = Mark.EMPTY;
                }
            }
        }
    }

    /**
     * Makes a copy of a board in its current state
     * @return board
     */
    public Board deepCopy() {
        Board copyBoard = new Board();

        for (int i = 0; i < DIM * 2 + 1; i++) {
            System.arraycopy(this.fields[i], 0, copyBoard.fields[i], 0, DIM * 2 + 1);
        }

        // If there are other non-primitive fields in your Board class, make sure to deep copy them too.

        return copyBoard;
    }

    /**
     * Returns true if the index of row and column is within the board else it returns false
     * @param row is the row
     * @param col is the column
     * @return true or false depending on row and column index
     */
    public boolean isField(int row, int col) {
        return row >= 0 && row < DIM * 2 + 1 && col >= 0 && col < DIM * 2 + 1;
    }

    /**
     * Checks whether the index given is valid meaning between and including 0 and 59
     * @param idx is index
     * @return true or false depending on index
     */
    public boolean isField(int idx) {
        return idx >= 0 && idx <= 59;
    }


    /**
     * Draws a horizontal line if the field is valid and empty
     * @param row is index of row
     * @param col is index of column
     * @return true or false depending on whether horizontal line is drawn
     */
    public boolean drawHorizontalLine(int row, int col) {
        if (isField(row, col) && fields[row][col] == Mark.EMPTY && row % 2 == 0 && col % 2 == 1) {
            fields[row][col] = Mark.HORIZONTAL_LINE;
            return true;
        }
        return false;
    }


    /**
     * Draws a vertical line if the field is valid and empty
     * @param row is index of row
     * @param col is index of column
     * @return true or false depending on whether vertical line is drawn
     */
    //@requires isField(row, col) && fields[row][col] == Mark.EMPTY && row % 2 == 1 && col % 2 == 0;
    public boolean drawVerticalLine(int row, int col) {
        if (isField(row, col) && fields[row][col] == Mark.EMPTY && row % 2 == 1 && col % 2 == 0) {
            fields[row][col] = Mark.VERTICAL_LINE;
            return true;
        }
        return false;
    }

    /**
     * The result is the type of mark situated in the given row and column index
     * @param row is index of row
     * @param col is index of column
     * @return mark type
     */
    //@pure
    public Mark getField(int row, int col) {
        if (isField(row, col)) {
            return fields[row][col];
        }
        return null;
    }

    /**
     * The result is the type of mark on the board with a given index
     * @param index is index of board
     * @return the mark
     */
    public Mark getField(int index) {
        if (isField(index)) {
            if (index >= 0 && index <= 4) {
                int row = 0;
                int col = 1+2*index;
                return (getField(row, col));
            }
            else if (index >= 11 && index <= 15) {
                int row = 2;
                int col = 2*index-21;
                return (getField(row, col));
            }
            else if (index >= 22 && index <= 26) {
                int row = 4;
                int col = 2*index-43;
                return (getField(row, col));
            }
            else if (index >= 33 && index <= 37) {
                int row = 6;
                int col = 2*index-65;
                return (getField(row, col));
            }
            else if (index >= 44 && index <= 48) {
                int row = 8;
                int col = 2*index-87;
                return (getField(row, col));
            }
            else if (index >= 55 && index <= 59) {
                int row = 10;
                int col = 2*index-109;
                return (getField(row, col));
            }
            else if (index >= 5 && index <= 10) {
                int row = 1;
                int col = 2*(index-5);
                return (getField(row, col));
            }
            else if (index >= 16 && index <= 21) {
                int row = 3;
                int col = 2*(index-16);
                return (getField(row, col));
            }
            else if (index >= 27 && index <= 32) {
                int row = 5;
                int col = 2*(index-27);
                return (getField(row, col));
            }
            else if (index >= 38 && index <= 43) {
                int row = 7;
                int col = 2*(index-38);
                return (getField(row, col));
            }
            else if (index >= 49 && index <= 54) {
                int row = 9;
                int col = 2*(index-49);
                return (getField(row, col));
            }
        }
        return null;
    }

    /**
     * The method is used to set a mark on the board with a given row and column index
     * @param row is index of row
     * @param col is index of column
     * @param mark is mark type to be set
     */
    //@requires mark != null;
    //@ensures getField(row, col) == mark;
    public void setField(int row, int col, Mark mark) {
        if (isField(row, col)) {
            fields[row][col] = mark;
        }
    }

    /**
     * This method uses setField(int row, int col, Mark mark), drawHorizontalLine and drawVerticalLine to draw a line and
     * set that line on the board using a given index
     * @param index is index of board
     */
    //@requires isField(index);
    //@ensures getField(index) != null;
    public void setField(int index) {
        if (isField(index)) {
            if (index >= 0 && index <= 4) {
                int row = 0;
                int col = 1+2*index;
                setField(row, col, Mark.HORIZONTAL_LINE);
                drawHorizontalLine(row, col);
            }
            else if (index >= 11 && index <= 15) {
                int row = 2;
                int col = 2*index-21;
                setField(row, col, Mark.HORIZONTAL_LINE);
                drawHorizontalLine(row, col);
            }
            else if (index >= 22 && index <= 26) {
                int row = 4;
                int col = 2*index-43;
                setField(row, col, Mark.HORIZONTAL_LINE);
                drawHorizontalLine(row, col);
            }
            else if (index >= 33 && index <= 37) {
                int row = 6;
                int col = 2*index-65;
                setField(row, col, Mark.HORIZONTAL_LINE);
                drawHorizontalLine(row, col);
            }
            else if (index >= 44 && index <= 48) {
                int row = 8;
                int col = 2*index-87;
                setField(row, col, Mark.HORIZONTAL_LINE);
                drawHorizontalLine(row, col);
            }
            else if (index >= 55 && index <= 59) {
                int row = 10;
                int col = 2*index-109;
                setField(row, col, Mark.HORIZONTAL_LINE);
                drawHorizontalLine(row, col);
            }
            else if (index >= 5 && index <= 10) {
                int row = 1;
                int col = 2*(index-5);
                setField(row, col, Mark.VERTICAL_LINE);
                drawVerticalLine(row, col);
            }
            else if (index >= 16 && index <= 21) {
                int row = 3;
                int col = 2*(index-16);
                setField(row, col, Mark.VERTICAL_LINE);
                drawVerticalLine(row, col);
            }
            else if (index >= 27 && index <= 32) {
                int row = 5;
                int col = 2*(index-27);
                setField(row, col, Mark.VERTICAL_LINE);
                drawVerticalLine(row, col);
            }
            else if (index >= 38 && index <= 43) {
                int row = 7;
                int col = 2*(index-38);
                setField(row, col, Mark.VERTICAL_LINE);
                drawVerticalLine(row, col);
            }
            else if (index >= 49 && index <= 54) {
                int row = 9;
                int col = 2*(index-49);
                setField(row, col, Mark.VERTICAL_LINE);
                drawVerticalLine(row, col);
            }
        }
    }

    /**
     * This method returns the number of squares on the board which is used after a move is made to see if there is a
     * difference between the number of squares before the move and number of squares after the move
     * @return number of squares
     */
    //@ensures \result == (\num_of int i, j; i >= 0 && i < DIM*2 && j >= 0 && j < DIM*2; fields[i][j + 1] == Mark.HORIZONTAL_LINE && fields[i + 1][j] == Mark.VERTICAL_LINE &&fields[i + 2][j + 1] == Mark.HORIZONTAL_LINE &&fields[i + 1][j + 2] == Mark.VERTICAL_LINE);
    public int numSquares() {
        int ns = 0;
        for (int i = 0; i < DIM * 2; i += 2) {
            for (int j = 0; j < DIM * 2; j += 2) {
                //The if statement checks if a square is formed by checking the marks of the surrounding index
                if (fields[i][j + 1] == Mark.HORIZONTAL_LINE &&
                        fields[i + 1][j] == Mark.VERTICAL_LINE &&
                        fields[i + 2][j + 1] == Mark.HORIZONTAL_LINE &&
                        fields[i + 1][j + 2] == Mark.VERTICAL_LINE) {
                    ns ++;
                }
            }
        }
        return ns;
    }

    /**
     * This method gives the value of the totalSquares field which is used to count the number of squares that were present before
     * the move was made
     * @return the total squares
     */
    public int getTotalSquares() {
        return totalSquares;
    }

    /**
     * This method is used to change the totalSquares field if the number of squares has increased after a move has been made
     * @param i is the number of squares to be set
     */
    public void changeSquares(int i) {
        totalSquares = i;
    }

    /**
     * Checks if all the index positions have been filled and hence checks if the game is over
     * @return if game is over
     */
    public boolean isGameOver() {
        for (int i = 0; i < DIM * 2; i += 2) {
            for (int j = 0; j < DIM * 2; j += 2) {
                //Checks if even a single index is empty returns false
                if (fields[i][j + 1] != Mark.HORIZONTAL_LINE ||
                        fields[i + 1][j] != Mark.VERTICAL_LINE ||
                        fields[i + 2][j + 1] != Mark.HORIZONTAL_LINE ||
                        fields[i + 1][j + 2] != Mark.VERTICAL_LINE) {
                    if (fields[i + 1][j + 1] == Mark.EMPTY) {
                        return false;
                    }
                }
            }
        }
        return true;
    }


    /**
     * This method is used to return the board in the form of a string in its current position
     * @return string of board
     */
    public String toString() {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < DIM * 2 + 1; i++) {
            for (int j = 0; j < DIM * 2 + 1; j++) {
                switch (fields[i][j]) {
                    case DOT:
                        sb.append(" * ");
                        break;
                    case HORIZONTAL_LINE:
                        sb.append("---");
                        break;
                    case VERTICAL_LINE:
                        sb.append(" | ");
                        break;
                    default:
                        sb.append("   ");
                        break;
                }
            }
            sb.append( "       " + indexBoard[i]);
            sb.append("\n");
        }
        return sb.toString();
    }

}
