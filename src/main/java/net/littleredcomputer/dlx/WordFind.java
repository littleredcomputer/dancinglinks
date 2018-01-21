package net.littleredcomputer.dlx;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

public class WordFind {
    private final int m, n;
    private final List<String> words = new ArrayList<>();
    private final String[][] gridPointNames;
    private static class Move {
        Move(int i, int j, char c) { this.i = i; this.j = j; this.c = c; }
        int i;
        int j;
        char c;
    }
    private final List<List<Move>> moves = new ArrayList<>();

    /**
     * Create a word find problem instance: in an m x n grid, position the given words.
     * @param m number of rows of grid
     * @param n number of columns of grid
     * @param words with which to fil grid
     */
    WordFind(int m, int n, Iterable<String> words) {
        this.m = m;
        this.n = n;
        for (String w : words) {
            this.words.add(w.toUpperCase());
        }
        gridPointNames = new String[m][n];
        for (int i = 0; i < m; ++i) {
            for (int j = 0; j < n; ++j) {
                gridPointNames[i][j] = i + "," + j;
            }
        }
    }

    /**
     * @return exhaustive stream of solutions of the word find (if any). The effort for any
     * given solution is expended only when that solution is demanded.
     */
    Stream<String> solutions() {
        return ExactCoverProblem.parseFrom(toProblem()).solutions().map(this::fromSolution);
    }

    private List<List<Move>> generatePlacements(String w, int i, int j) {
        final int N = w.length();

        List<List<Move>> result = new ArrayList<>();

        Consumer<Function<Integer, Move>> m = (Function<Integer, Move> f) ->
                result.add(IntStream.range(0, N).boxed().map(f).collect(Collectors.toList()));

        if (j + N <= n) m.accept(k -> new Move(i, j+k, w.charAt(k)));  // W to E
        if (i + N <= this.m) m.accept(k -> new Move(i+k, j, w.charAt(k)));  // N to S
        if (j - N >= -1) m.accept(k -> new Move(i, j-k, w.charAt(k)));  // E to W
        if (i - N >= -1) m.accept(k -> new Move(i-k, j, w.charAt(k)));  // S to N
        if (i + N <= this.m && j + N <= n) m.accept(k -> new Move(i+k, j+k, w.charAt(k)));  // NW to SE
        if (i - N >= -1 && j - N >= -1) m.accept(k -> new Move(i-k, j-k, w.charAt(k)));  // SE to NW
        if (i - N >= -1 && j + N <= n) m.accept(k -> new Move(i-k, j+k, w.charAt(k)));  // SW to NE
        if (i + N <= this.m && j - N >= -1) m.accept(k -> new Move(i+k, j-k, w.charAt(k)));  // NE to SW
        return result;
    }

    private void wordOptions(StringBuilder p, String w) {
        for (int i = 0; i < m; ++i) {
            for (int j = 0; j < n; ++j) {
                generatePlacements(w, i, j).forEach(ms -> {
                    moves.add(ms);
                    p.append(w).append(' ');
                    ms.forEach(m -> p.append(gridPointNames[m.i][m.j]).append(':').append(m.c).append(' '));
                    p.append('\n');
                });
            }
        }
    }

    private String toProblem() {
        StringBuilder p = new StringBuilder();
        // primary items: the words
        for (String w : words) {
            p.append(w).append(' ');
        }
        p.append("; ");
        // secondary items: the grid points
        for (int i = 0; i < m; ++i) {
            for (int j = 0; j < n; ++j) {
                p.append(gridPointNames[i][j]).append(' ');
            }
        }
        p.append('\n');
        //
        words.forEach(w -> wordOptions(p, w));
        return p.toString();
    }

    private String fromSolution(List<Integer> options) {
        char board[][] = new char[m][n];
        for (int i = 0; i < m; ++i) {
            for (int j = 0; j < n; ++j) {
                board[i][j] = '\u00b7';
            }
        }
        options.forEach(index -> moves.get(index).forEach(m -> board[m.i][m.j] = m.c));
        StringBuilder s = new StringBuilder();
        for (int i = 0; i < m; ++i) {
            for (int j = 0; j < n; ++j) {
                s.append(board[i][j]);
            }
            s.append('\n');
        }
        return s.toString();
    }
}
