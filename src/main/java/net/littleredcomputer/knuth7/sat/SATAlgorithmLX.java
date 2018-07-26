package net.littleredcomputer.knuth7.sat;

import gnu.trove.list.array.TIntArrayList;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

public class SATAlgorithmLX extends SATAlgorithmL {
    private static final Logger log = LogManager.getFormatterLogger();
    // The data structures CINX, CSIZE are used in the WIDE form (k-SAT where k > 3) of Algorithm L.
    private final List<List<SATAlgorithmL.Literal>> CINX = new ArrayList<>();
    private final TIntArrayList CSIZE = new TIntArrayList();

    SATAlgorithmLX(SATProblem p) {
        /* XXX put the name in here */
        super("LX", p);
        addClauses();
    }

    /**
     * Adds a wide clause to the solver's data structures.
     * A new entry in CINX is made, and every involved literal's KINX table receives the index of the new CINX entry.
     * CSIZE and KSIZE are maintained.
     * @param clause in encoded literal index form
     */
    @Override void addClause(List<Integer> clause) {
        final int k = CINX.size();
        List<Literal> c = clause.stream().map(l -> lit[l]).collect(Collectors.toList());
        CINX.add(c);
        CSIZE.add(c.size());
        c.forEach(l -> {
            l.KINX.add(k);
            ++l.KSIZE;
        });
    }

    @Override void printTable() {
        log.trace("WIDE tables");
        for (int i = 0; i < CINX.size(); ++i) {
            final int n = CSIZE.getQuick(i);
            if (n > 0) {
                log.trace("CINX(%d) = %s", i, CINX.get(i).stream().limit(n).map(Literal::toString).collect(Collectors.joining(", ")));
            }
        }
    }

    @Override boolean deactivate(Literal L) {
        for (int xi = poslit(L.var.id); xi <= neglit(L.var.id); ++xi) {
            final Literal l = lit[xi];  // for l in {L, ~L}
            for (int i = 0; i < l.KSIZE; ++i) {
                final int c = l.KINX.getQuick(i);  // for each clause c containing l
                List<Literal> clause = CINX.get(c);
                // find l in clause, move it to the end, and shorten the clause
                int s = --u.KSIZE;
                int j = clause.indexOf(l);
                if (j < 0) throw new IllegalStateException("internal error: damaged wide index");
                if (j >= CSIZE.get(j)) throw new IllegalStateException("internal error: literal was found in inactive part of the clause data")

                    final List<Literal> clause = CINX.get(j);
                    for (int k = 0; k < CSIZE.getQuick(j); ++k) {
                        final Literal u = clause.get(k);
                        final int t = u.KINX.indexOf(c);  // find the t <= s for which KINX(u)[t] == c
                        if (t < 0) throw new
                        if (t != s) {
                            u.KINX.set(t, u.KINX.getQuick(s));
                            u.KINX.set(s, c);
                        }
                        // TODO: implement the heuristic in the ans. to ex 143
                    }
                }
            }
        }
        for (int i = 0; i < L.not.KSIZE; ++i) {
            final int c = L.not.KINX.getQuick(i);
            int s = CSIZE.getQuick(c) - 1;
            CSIZE.set(c, s);
            if (s == 2) {
                // Find the two free literals (u, v) in CINX(c), swap them into the first
                // positions of that list, put them on a temporary stack, and swap c out of the
                // clause lists of u and v as above.

                // i.e.: there were 3 literals, and now there are two. Swapping the
                // 3rd guy into the third position if necessary should leave the two
                // free literals at the head of the list.
            }
        }
        // Finally step L7' does step L8' = L8 for all (u, v) on the temporary stack.
        return true; /* XXX */
    }

    @Override void reactivate(Variable X) {
        throw new IllegalStateException("don't know how to do this yet");
    }

    @Override float[] computeHeuristics() {
        return new float[0];
    }

    @Override
    protected boolean Perform72(Literal l) {
        return false;
    }

    @Override
    protected boolean Perform73(Literal l) {
        return false;
    }
}
