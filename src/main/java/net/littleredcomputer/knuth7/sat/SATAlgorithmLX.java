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
    private static final float epsilon = 0.001f;
    private static final float gamma = 0.2f;
    // The data structures CINX, CSIZE are used in the WIDE form (k-SAT where k > 3) of Algorithm L.
    private final List<List<SATAlgorithmL.Literal>> CINX = new ArrayList<>();
    private final TIntArrayList CSIZE = new TIntArrayList();
    private final float[] h;
    private final int maxClause;
    private final float[] clauseWeight;
    private final Deque<Literal> bstack = new ArrayDeque<>();



    SATAlgorithmLX(SATProblem p) {
        /* XXX put the name in here */
        super("LX", p);
        addClauses();
        h = new float[2 * nVariables + 2];
        maxClause = CSIZE.max();
        clauseWeight = new float[maxClause];
        clauseWeight[2] = 1f;
        for (int k = 3; k < maxClause; ++k) clauseWeight[k] = clauseWeight[k-1] * gamma + 0.01f;
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
        for (int i = 2; i < 2*nVariables+2; ++i) {
            final Literal l = lit[i];
            if (l.KSIZE > 0) {
                log.trace("KINX(%s) = %s", l, l.KINX.subList(0, l.KSIZE));
            }
        }
    }

    @Override boolean deactivate(Literal L) {
        if (tracing.contains(Trace.BIMP)) log.trace( "<-- DEACTIVATE %s", L);
        // Remove the formerly free variable |L| from the data structures.
        // First deactivate all of the active big clauses that contain L:
        for (int i = 0; i < L.KSIZE; ++i) {
            final int c = L.KINX.getQuick(i);
            final List<Literal> us = CINX.get(c);
            // At most CSIZE(c) literals in us can be free, so we can break early when we have seen that many.
            // In general, though, they need not appear at the front of the list
            for (int j = 0, n = 0; j < us.size() && n < CSIZE.getQuick(c); ++j) {
                final Literal u = us.get(j);
                if (isfree(u)) {
                    swapOutOfClauseList(c, u);
                    ++n;
                }
            }
            // TODO: implement the free-sorting heuristic here
        }
        final Literal notL = L.not;
        Deque<Pair<Literal, Literal>> stack = new ArrayDeque<>();  // TODO: eliminate allocation
        // Update the clauses for which L has become false
        for (int i = 0; i < notL.KSIZE; ++i) {
            final int c = notL.KINX.getQuick(i);
            int s = CSIZE.getQuick(c) - 1;
            if (tracing.contains(Trace.BIMP)) log.trace("Removing %s from clause #%d %s", notL, c, s == 2 ? "*" : "");
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
                // NB: Knuth suggests that swapping may need to happen, but does it? Hasn't the previous step taken care of that?
                assert clause.get(2) == notL;
                final Literal u = clause.get(0), v = clause.get(1);
                stack.push(new Pair<>(u, v));  // TODO: eliminate allocation
                swapOutOfClauseList(c, u);
                swapOutOfClauseList(c, v);
            }
        }
        // Finally step L7' does step L8' = L8 for all (u, v) on the temporary stack.
        // Do step L8 for all pairs (u,v) in TIMP(L) then return to L6.

        // XXX see sat11k.ch line 604: we choose the new participants differently.
        // XXX see sat11k.ch line 742 for the algorithm to establish a new participant.

        while (!stack.isEmpty()) {
            Pair<Literal, Literal> top = stack.pop();
            final Literal u = top.getKey(), v = top.getValue();
            if (tracing.contains(Trace.FIXING)) log.trace("  %s->%s|%s", L, u, v);
            // makeParticipants(u.var, v.var);
            if (!consider(u, v)) return false;
        }
        return true;
    }

    private void swapOutOfClauseList(int clauseIndex, Literal u) {
        if (tracing.contains(Trace.BIMP)) log.trace("Removing #%d from %s's clause list", clauseIndex, u);
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
        if (tracing.contains(Trace.BIMP)) log.trace("--> REACTIVATE %s", L);
        final Literal notL = L.not;
        for (int i = notL.KSIZE - 1; i >= 0; --i) {
            final int c = notL.KINX.getQuick(i);
            // proceeding in reverse order from the order used in L7'...
            final int s = CSIZE.getQuick(c);
            final List<Literal> cinxC = CINX.get(c);
            CSIZE.set(c, s+1);
            if (tracing.contains(Trace.BIMP)) log.trace("Adding %s to clause #%d", cinxC.get(s), c);
            if (s == 2) {
                // swap c back into the clause lists of u and v, where u = CINX(c)[0] and v = CINX(c)[1].
                final Literal u = cinxC.get(0), v = cinxC.get(1);
                ++v.KSIZE;
                ++u.KSIZE;
                if (tracing.contains(Trace.BIMP)) {
                    log.trace("Adding #%d to %s's clause list", v.KINX.getQuick(v.KSIZE-1), v);
                    log.trace("Adding #%d to %s's clause list", u.KINX.getQuick(u.KSIZE-1), u);
                }
            }
        }
        for (int i = L.KSIZE - 1; i >= 0; --i) {
            final int c = L.KINX.getQuick(i);
            final List<Literal> clause = CINX.get(c);
            for (int j = clause.size() - 1, n = 0; n < CSIZE.getQuick(c) && j >= 0; --j) {
                final Literal u = clause.get(j);
                if (isfree(u)) {
                    // for each of the CSIZE(c) free literals u in CINX(c), again proceeding in reverse order from
                    // the order used in L7', swap c back into the clause list of u (which, by design, is just an
                    // increment of the size)
                    ++clause.get(j).KSIZE;
                    if (tracing.contains(Trace.BIMP)) log.trace("Adding #%d to %s's clause list", clause.get(j).KINX.getQuick(clause.get(j).KSIZE-1), clause.get(j));
                }
            }
        }
    }

    @Override float[] computeHeuristics() {
        // DEK write: "Good results have been obtained with the simple formula
        //   h(l) = ε + KSIZE(lbar) + sum(u in BIMP(l), u free; KSIZE(ubar))
        // which estimates the potential number of big-clause reductions that occur when l becomes true.
        // ε is typically set to 0.001.
        for (int i = 2; i < 2 * nVariables + 2; ++i) {
            final Literal l = lit[i];
            h[i] = epsilon + l.not.KSIZE;
            for (int j = 0; j < l.BSIZE; ++j) {
                final Literal u = l.BIMP.get(i);
                if (isfree(u)) h[i] += u.not.KSIZE;
            }
        }
        return h;
    }

    /* @ Windfalls and the weighted potentials for new binaries are discovered here,
       as we ``virtually remove'' |bar(ll)| from the active clauses in which it
       appears.

       If all but one of the literals in such a clause has now been fixed false
       at the current level, we put the remaining one on |bstack| for subsequent
       analysis.

       A conflict arises if all literals are fixed false. In such cases we set
       |bptr=-1| instead of going immediately to |contra|; otherwise
       backtracking would be more complicated. */
    @Override
    protected boolean Perform72(Literal l) {
        // @ We've implicitly removed |bar(looklit)| from all of the active clauses.
        // Now we must put it back, if its truth value was set at a lower level
        // than~|cs|.
        ResetFptr();
        W.clear();


        boolean contra = false;
        bstack.clear();
        if (tracing.contains(Trace.LOOKAHEAD)) log.trace(" (%s lookout)", l);
        for (int i = 0; i < l.not.KSIZE; ++i) {
            final int c = l.not.KINX.getQuick(i);
            int s = CSIZE.get(c) - 1;
            CSIZE.set(c, s);
            if (s >= 2) w += clauseWeight[s];
            else if (!contra) {
                Literal u = null;
                final List<Literal> clause = CINX.get(c);
                // put the last remaining literal of c into bstack
                int j = 0;
                for (; j < clause.size(); ++j) {
                    u = clause.get(j);
                    Fixity fu = fixity(u);
                    if (fu == Fixity.UNFIXED) break;
                    if (fu == Fixity.FIXED_F) continue;;
                    u = null;
                    break;  // clause c is satisfied
                }
                if (j == clause.size()) {
                    contra = true;
                    if (tracing.contains(Trace.LOOKAHEAD)) log.trace("  looking %s-> [%d]", l, c);
                } else if (u != null) {
                    bstack.push(u);
                    if (tracing.contains(Trace.LOOKAHEAD)) log.trace("  looking %s->%s [%d]", l, u, c);
                }
            }
        }
        if (contra) return false;
        while (!bstack.isEmpty()) {
            Literal u = bstack.pop();
            if (fixity(u) == Fixity.FIXED_F) return false;
            W.push(u);
            if (!propagate(u)) return false;
        }
        return true;
    }



    @Override
    protected boolean Perform73(Literal l) {
        throw new IllegalStateException("not ready");
    }

    @Override
    void ResetFptr() {
        // Reset fptr by removing unfixed literals from rstack
        while (E > F) {
            final Literal u = R[E-1];
            if (isfixed(u)) break;
            --E;
            if (tracing.contains(Trace.LOOKAHEAD)) log.trace(" (%s lookin)", u.not);
            // unreduce all big clauses that contained bar(u) during lookahead
            unreduceBigClausesContaining(u.not);
        }
    }

    private void unreduceBigClausesContaining(Literal u) {
        for (int i = u.KSIZE - 1; i >= 0; --i) {
            final int c = u.KINX.getQuick(i);
            CSIZE.set(c, CSIZE.get(c) + 1);
        }
    }
}
