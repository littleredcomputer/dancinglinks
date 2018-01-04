public class Sudoku {
    private int[][] constraints = new int[9][9];  // What choices remain valid for cell i,j?
    private int[] rows = new int[9];              // What numbers are free in row i?
    private int[] columns = new int[9];           // What numbers are free in column j?
    private int[] boxes = new int[9];             // What numbers are free in box k?
    private int[][] board = new int[9][9];

    private Sudoku() {
        // Initially all moves are possible; record possibilities as bitvectors
        int mask = (1<<9) - 1;
        for (int i = 0; i < board.length; ++i) {
            rows[i] = columns[i] = boxes[i] = mask;
            for (int j = 0; j < board[i].length; ++j) {
                constraints[i][j] = mask;
                board[i][j] = 0;
            }
        }
    }

    /**
     * @param r row index [0..9)
     * @param c column index [0..9)
     * @param n contents of cell [1..9]
     */
    private void addEntry(int r, int c, int n) {
        int index = n-1;
        int mask = 1 << index;
        rows[r] &= ~mask;
        columns[c] &= ~mask;
        board[r][c] = n;
        // Make sure this placement is valid...
        if ((constraints[r][c] & mask) == 0) {
            throw new IllegalArgumentException(
                    String.format("uniqueness violation for entry %d @ %d,%d %x", n, r, c, constraints[r][c]));
        }
        // ...and then assert that there are no remaining options for this cell
        constraints[r][c] = 0;
        // The consequences of this value: it is unique on its row/column...
        for (int k = 0; k < 9; k++) {
            constraints[r][k] &= ~mask;
            constraints[k][c] &= ~mask;
        }
        // And unique within its box.
        int br = r / 3;
        int bc = c / 3;
        boxes[br * 3 + bc] &= ~mask;
        for (int brr = br * 3; brr < (br + 1) * 3; ++brr) {
            for (int bcc = bc * 3; bcc < (bc + 1) * 3; ++bcc) {
                constraints[brr][bcc] &= ~mask;
            }
        }
    }

    public static Sudoku fromBoardString(String boardString) {
        // A board might look like:
        // "..3 .1. ... 415 ... .9. 2.6" etc.
        // Digits fill boxes, left to right, top to bottom; whitespace is ignored, '.' represents an empty box.
        Sudoku sudoku = new Sudoku();

        int p = 0;
        for (int j = 0; j < boardString.length(); ++j) {
            char ch = boardString.charAt(j);
            if (ch > '0' && ch <= '9') {
                int r = p / 9;
                int c = p % 9;
                int number = ch - '0';   // 1..9

                sudoku.addEntry(r, c, number);
                ++p;
            } else if (ch == '.') {
                ++p;
            }
        }
        return sudoku;
    }

    public ExactCoverProblem toProblem() {
        StringBuilder sb = new StringBuilder();
        // Attach the items pij, rij, cij, bij for i = 1..9, j = 1..9
        for (int i = 0; i < 9; ++i) {
            for (int j = 0; j < 9; ++j) {
                if (board[i][j] == 0) sb.append("p").append(i).append(j).append(' ');
                int mask = 1 << j;
                if ((rows[i] & mask) != 0) sb.append("r").append(i).append(j + 1).append(' ');
                if ((columns[i] & mask) != 0) sb.append("c").append(i).append(j + 1).append(' ');
                if ((boxes[i] & mask) != 0) sb.append("b").append(i).append(j + 1).append(' ');
            }
        }
        sb.append('\n');
        for (int i = 0; i < 9; ++i) {
            for (int j = 0; j < 9; ++j) {
                int bits = constraints[i][j];
                if (bits > 0) {
                    System.out.printf("%d %d: ", i, j);
                    for (int k = 0; k < 9; ++k) {
                        if ((bits & (1<<k)) != 0) {
                            sb.append('p').append(i).append(j).append(' ');
                            sb.append('r').append(i).append(k+1).append(' ');
                            sb.append('c').append(j).append(k+1).append(' ');
                            sb.append('b').append(3 * (i/3) + j/3).append(k+1).append(' ');
                            sb.append('\n');
                            System.out.printf("%d ", k+1);
                        }
                    }
                    System.out.println();
                }
            }
        }
        System.out.println(sb.toString());
        return new ExactCoverProblem().parse(sb.toString());
    }
}
