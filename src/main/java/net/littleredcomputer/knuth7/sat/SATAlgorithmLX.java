package net.littleredcomputer.knuth7.sat;

import gnu.trove.list.array.TIntArrayList;
import javafx.util.Pair;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
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
        // Remove the formerly free variable |L| from the data structures.
        // First deactivate all of the active big clauses that contain L:


        for (int i = 0; i < L.KSIZE; ++i) {
            final int c = L.KINX.getQuick(i), N = CSIZE.getQuick(c);
            final List<Literal> us = CINX.get(c);
            for (int j = 0; j < N; ++j) {
                final Literal u = us.get(j);
                swapOutOfClauseList(c, u);
            }
        }
        final Literal notL = L.not;
        Deque<Pair<Literal, Literal>> stack = new ArrayDeque<>();  // TODO: eliminate allocation
        // Update the clauses for which L has become false
        for (int i = 0; i < notL.KSIZE; ++i) {
            final int c = notL.KINX.getQuick(i);
            int s = CSIZE.getQuick(c) - 1;
            CSIZE.set(c, s);
            // find notL in the clause; swap it into the end position
            final List<Literal> clause = CINX.get(c);
            int t = clause.indexOf(notL);
            if (t != s) {
                assert t < s;
                clause.set(t, clause.get(s));
                clause.set(s, notL);
            }
            if (s == 2) {
                // Find the two free literals (u, v) in CINX(c), swap them into the first
                // positions of that list, put them on a temporary stack, and swap c out of the
                // clause lists of u and v as above.
                final Literal u = clause.get(0), v = clause.get(1);
                stack.push(new Pair<>(u, v));  // TODO: eliminate allocation
                swapOutOfClauseList(c, u);
                swapOutOfClauseList(c, v);
            }
        }
        // Finally step L7' does step L8' = L8 for all (u, v) on the temporary stack.
        // Do step L8 for all pairs (u,v) in TIMP(L) then return to L6.
        while (!stack.isEmpty()) {
            Pair<Literal, Literal> top = stack.pop();
            final Literal u = top.getKey(), v = top.getValue();
            if (tracing.contains(Trace.FIXING)) log.trace("  %s->%s|%s", L, u, v);
            makeParticipants(u.var, v.var);
            if (!consider(u, v)) return false;
        }
        return true;
    }

    private void swapOutOfClauseList(int clauseIndex, Literal u) {
        // Swap c out of u's clause list
        final int s = --u.KSIZE;
        // Find the t <= s with KINX(u)[t] == c
        final TIntArrayList kinxU = u.KINX;
        final int t = kinxU.indexOf(clauseIndex);
        if (t != s) {
            assert t < s;
            kinxU.set(t, kinxU.getQuick(s));
            kinxU.set(s, clauseIndex);
        }
        // TODO: implement heuristic
    }

    @Override void reactivate(Literal L) {
        final Literal notL = L.not;
        for (int i = notL.KSIZE - 1; i >= 0; --i) {
            final int c = notL.KINX.getQuick(i);
            // proceeding in reverse order from the order used in L7'...
            final int s = CSIZE.getQuick(c);
            CSIZE.set(c, s+1);
            if (s == 2) {
                // swap c back into the clause lists of u and v, where u = CINX(c)[0] and v = CINX(c)[1].
                ++CINX.get(c).get(0).KSIZE;
                ++CINX.get(c).get(1).KSIZE;
            }
        }
        for (int i = L.KSIZE - 1; i >= 0; --i) {
            final int c = L.KINX.getQuick(i);
            final List<Literal> clause = CINX.get(c);
            for (int j = CSIZE.get(c) - 1; j >= 0; --j) {
                // for each of the CSIZE(c) free literals u in CINX(c), again proceeding in referse order from
                // the order used in L7', swap c back into the clause list of u (which, by design, is just an
                // increment of the size)
                ++clause.get(j).KSIZE;
            }
        }
    }

    @Override float[] computeHeuristics() {
        throw new IllegalStateException("not ready");
    }

    @Override
    protected boolean Perform72(Literal l) {
        throw new IllegalStateException("not ready");
    }

    @Override
    protected boolean Perform73(Literal l) {
        throw new IllegalStateException("not ready");
    }
}
