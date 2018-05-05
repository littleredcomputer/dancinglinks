package net.littleredcomputer.knuth7;

import com.google.common.base.CharMatcher;
import com.google.common.base.Splitter;
import com.google.common.collect.Sets;

import java.util.*;

/*
 * See also: Bain S. (2007) Time-Reversal in Conway’s Life as SAT. In: Orgun M.A., Thornton J. (eds)
 * AI 2007: Advances in Artificial Intelligence. AI 2007. Lecture Notes in Computer Science,
 * vol 4830. Springer, Berlin, Heidelberg
 */

public class Life {
    private final static Splitter splitter = Splitter.onPattern("\\s").omitEmptyStrings().trimResults();
    private final static CharMatcher dot = CharMatcher.anyOf(".\u00b7");
    final int r;
    final int c;
    final boolean x[][];

    Life(int r, int c) {
        this.r = r;
        this.c = c;
        x = new boolean[r][];
        for (int i = 0; i < r; ++i) x[i] = new boolean[c];
    }

    static Life fromDots(String s) {
        List<String> rows = splitter.splitToList(s);
        if (rows.isEmpty()) throw new IllegalArgumentException("bad board");
        int r = rows.size();
        int c = rows.get(0).length();
        for (int i = 1; i < r; ++i) {
            if (rows.get(i).length() != c) throw new IllegalArgumentException("ragged board");
        }
        Life l = new Life(r, c);
        for (int i = 0; i < r; ++i) {
            for (int j = 0; j < c; ++j) {
                l.x[i][j] = !dot.matches(rows.get(i).charAt(j));
            }
        }
        return l;
    }

    private int nu(int i, int j) {
        int n = 0;
        for (int dx = -1; dx <= 1; ++dx) {
            for (int dy = -1; dy <= 1; ++dy) {
                if (dx != 0 || dy != 0) {
                    int R = i + dx, C = j + dy;
                    if (R >= 0 && R < r && C >= 0 && C < c && x[R][C]) ++n;
                }
            }
        }
        return n;
    }

    Life step() {
        Life y = new Life(r, c);
        for (int i = 0; i < r; ++i) {
            for (int j = 0; j < c; ++j) {
                int n = nu(i, j);
                // live: 2 or 3, dead 3.
                y.x[i][j] = x[i][j] ? (n == 2 || n == 3) : n == 3;
            }
        }
        return y;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        Life life = (Life) o;
        return r == life.r && c == life.c && Arrays.deepEquals(x, life.x);
    }

    @Override
    public int hashCode() {
        int result = Objects.hash(r, c);
        result = 31 * result + Arrays.deepHashCode(x);
        return result;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < r; ++i) {
            for (int j = 0; j < c; ++j) sb.append(x[i][j] ? '*' : '\u00b7');
            sb.append('\n');
        }
        return sb.toString();
    }



    /**
     * This is currently the naive clause set for finding an ancestor of a
     * life tableau.
     * @return
     */
    public SATProblem ancestor() {
        // Ancestor is sort of like the inverse of step: Given the tableau
        // one step in the future, find a tableau that could have led there.
        // We don't do that ourselves, but instead prepare an instance of
        // SAT which can compute such a tableau, if one exists.
        int tstep = 1;
        int nextVar = 0;

        // Our goal is to define a collection of variables, one for each cell
        // of the ancestor state, and constrain them so that the ensemble of
        // cells generate the goal tableau.

        // At the bottom, we have the truth values of the goal tableau.
        // The next level up will consist of variables describing the state
        // of the previous step.

        List<List<Integer>> clauses = new ArrayList<>();

        // TODO: consider whether this code should be homogenized in the sense
        // of just always considering the goal state to be variables and then
        // appending a collection of unit clauses to enforce the final state.

        Set<Integer> N = new TreeSet<>();
        for (int i = 0; i < r; ++i) {
            for (int j = 0; j < c; ++j) {
                // The clause generation here follows the formulation in Bain, which
                // differs slightly from that in Knuth.

                //
                // y is the state of cell (i,j) in the next (i.e., given) step.
                boolean y = x[i][j];
                // x is the variable representing the state of x in the ancestor step (one-based).
                int x = i*c+j+1;
                // N contains the set of variables representing the neighbors of cell (i,j) in
                // the ancestor step (the step to be solved for). It will typically contain
                // eight variables--fewer at boundary points. The variables are numbered in
                // row-major order, starting from 1.
                N.clear();
                for (int dx = -1; dx <= 1; ++dx) {
                    for (int dy = -1; dy <= 1; ++dy) {
                        if (dx != 0 || dy != 0) {
                            int xp = i+dx;
                            int yp = j+dy;
                            if (xp >= 0 && xp < r && yp >= 0 && yp < c) N.add(xp*c+yp+1);
                        }
                    }
                }
                // Loneliness: (8 choose 7) clauses of the form ~y x1 ... x7
                // "we are not alive if we had seven or more dead neighbors"
                // In corner cases, the cells outside the bounding box
                // automatically qualify as dead, so they do not need to
                // be a part of the clause; in effect, we need all subsets
                // of one less than the number of neigbors we have. Further,
                // if y is false, then all these clause are automatically satisfied.
                if (y) {
                    for (Set<Integer> nbrs : Sets.combinations(N, N.size()-1)) {
                        List<Integer> clause = new ArrayList<>(nbrs);
                        // clause.add(-y);
                        clauses.add(clause);
                    }
                }
                // Stagnation: (8 choose 2) clauses of the form ~y x ~x1 ~x2 x3 ... x8
                // "we are not alive if we were dead and had exactly two live neighbors"
                if (y && N.size() >= 2) {
                    for (Set<Integer> negative : Sets.combinations(N, 2)) {
                        Set<Integer> positive = Sets.difference(N, negative);
                        List<Integer> clause = new ArrayList<>(positive);
                        negative.forEach(n -> clause.add(-n));
                        // clause.add(-y);
                        clause.add(x);
                        clauses.add(clause);
                    }
                }
                // Overcrowding: (8 choose 4) clauses of the form ~y ~x1 ~x2 ~x3 ~x4
                // "we are not alive if we had four or more live neighbors"
                if (y && N.size() >= 4) {
                    for (Set<Integer> nbrs : Sets.combinations(N, 4)) {
                        List<Integer> clause = new ArrayList<>();
                        // clause.add(-y);
                        nbrs.forEach(n -> clause.add(-n));
                        clauses.add(clause);
                    }
                }
                // Preservation: (8 choose 2) clauses of the form y ~x ~x1 ~x2 x3 ... x8
                // "we are not dead if we were alive and had exactly two live neighbors"
                // TODO: fold this together with stagnation, to avoid recomputing the 2-subsets
                if (!y && N.size() >= 2) {
                    for (Set<Integer> negative : Sets.combinations(N, 2)) {
                        Set<Integer> positive = Sets.difference(N, negative);
                        List<Integer> clause = new ArrayList<>(positive);
                        // clause.add(y)
                        clause.add(-x);
                        negative.forEach(n -> clause.add(-n));
                        clauses.add(clause);
                    }
                }
                // Life: (8 choose 3) clauses of the form y ~x1 ~x2 ~x3 x4 ... x8
                // "we are not dead if we had exactly 3 live neighbors"
                if (!y && N.size() >= 3) {
                    for (Set<Integer> negative : Sets.combinations(N, 3)) {
                        Set<Integer> positive = Sets.difference(N, negative);
                        List<Integer> clause = new ArrayList<>(positive);
                        // clause.add(y);
                        negative.forEach(n -> clause.add(-n));
                        clauses.add(clause);
                    }
                }
            }
        }
        // ok, now we have all the clauses.
        SATProblem p = new SATProblem(r*c);
        clauses.forEach(p::addClause);
        return p;
    }

    static Life fromSolution(int r, int c, boolean[] bs) {
        Life l = new Life(r, c);
        for (int i = 0; i < r; ++i) {
            System.arraycopy(bs, i * c, l.x[i], 0, c);
        }
        return l;
    }
}
