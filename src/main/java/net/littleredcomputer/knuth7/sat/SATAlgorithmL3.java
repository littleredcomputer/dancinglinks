package net.littleredcomputer.knuth7.sat;

import gnu.trove.list.array.TIntArrayList;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.BiFunction;

public class SATAlgorithmL3 extends SATAlgorithmL {
    private static final Logger log = LogManager.getFormatterLogger();

    // The data structures U, V, LINK and NEXT are used in the 3-SAT optimized form of Algorithm L.
    private final List<Literal> U = new ArrayList<>();
    private final List<Literal> V = new ArrayList<>();
    private final TIntArrayList LINK = new TIntArrayList();
    private final TIntArrayList NEXT = new TIntArrayList();
    private final TIntArrayList buf = new TIntArrayList();
    private final float[][] h;  // h[d][l] is the h-score ("rough heuristic") of literal l at depth d
    private final float[] hprime;  // storage for refinement steps of heuristic score
    private final float alpha = 3.5f;
    private final float THETA = 20.0f;


    public SATAlgorithmL3(SATProblem p) {
        super("L3", p); /* XXX once L becomes abstract also pass the name */
        h = new float[nVariables + 1][];
        hprime = new float[2 * p.nVariables() + 2];
        addClauses();
    }

    /**
     * Adds a 3-clause to the TIMP database.
     *
     * @param clause in encoded literal index form
     */
    @Override
    void addClause(List<Integer> clause) {
        if (clause.size() != 3) throw new IllegalArgumentException("The L3 solver only applies to 3-SAT problems");
        final Literal w = lit[clause.get(0)], v = lit[clause.get(1)], u = lit[clause.get(2)];
        int z = U.size();
        U.add(v);
        V.add(w);

        U.add(w);
        V.add(u);

        U.add(u);
        V.add(v);

        LINK.add(z + 1);
        LINK.add(z + 2);
        LINK.add(z);

        NEXT.add(u.not.TIMP);
        NEXT.add(v.not.TIMP);
        NEXT.add(w.not.TIMP);

        u.not.TIMP = z;
        v.not.TIMP = z + 1;
        w.not.TIMP = z + 2;

        ++u.not.TSIZE;
        ++v.not.TSIZE;
        ++w.not.TSIZE;
    }

    private boolean timpForEach(Literal l, BiFunction<Literal, Literal, Boolean> f) {
        for (int p = l.TIMP, i = 0; i < l.TSIZE; p = NEXT.get(p), ++i) {
            Literal u = U.get(p), v = V.get(p);
            if (!f.apply(u, v)) return false;
        }
        return true;
    }

    private String timpToString(Literal l) {
        StringBuilder sb = new StringBuilder();
        sb.append(String.format("  %3s -> ", l));
        timpForEach(l, (u, v) -> {
            sb.append(u).append('|').append(v).append(' ');
            return true;
        });
        return sb.toString();
    }

    @Override
    void printTable() {
        log.trace("TIMP tables:");
        for (int i = 1; i < lit.length; ++i) {
            final Literal l = lit[i];
            if (l.TSIZE > 0) {
                log.trace(timpToString(l));
            }
        }
    }

    /**
     * This is the heart of step L7 in the 3-SAT case. The suppressed variable is moved
     * to the end of the TIMP lists and the corresponding sizes are dropped to conceal the
     * variable in a way that is easy to reverse upon backtracking (by just restoring the
     * original sizes).
     *
     * @param L Literal whose variable to hide.
     */
    @Override
    boolean deactivate(Literal L) {
        // kind of silly?
        for (int xi = poslit(L.var.id); xi <= neglit(L.var.id); ++xi) {
            final Literal l = lit[xi];
            for (int p = l.TIMP, tcount = 0; tcount < l.TSIZE; p = NEXT.get(p), ++tcount) {
                Literal u0 = U.get(p), v = V.get(p);
                int pp = LINK.get(p);
                int ppp = LINK.get(pp);
                int s = --u0.not.TSIZE;
                int t = u0.not.TIMP;
                for (int i = 0; i < s; ++i) t = NEXT.get(t);
                if (pp != t) {
                    final Literal uu = U.get(t), vv = V.get(t);
                    int q = LINK.get(t);
                    int qq = LINK.get(q);
                    LINK.set(qq, pp);
                    LINK.set(p, t);
                    U.set(pp, uu);
                    V.set(pp, vv);
                    LINK.set(pp, q);
                    U.set(t, v);
                    V.set(t, l.not);
                    LINK.set(t, ppp);

                    // NOT IN KNUTH: reset pp.
                    pp = t;
                    // END NOT IN KNUTH
                }
                // Then set...
                s = --v.not.TSIZE;
                t = v.not.TIMP;
                for (int i = 0; i < s; ++i) t = NEXT.get(t);
                if (ppp != t) {  // swap pairs by setting
                    final Literal uu = U.get(t), vv = V.get(t);
                    int q = LINK.get(t);
                    int qq = LINK.get(q);
                    LINK.set(qq, ppp);
                    LINK.set(pp, t);
                    U.set(ppp, uu);
                    V.set(ppp, vv);
                    LINK.set(ppp, q);
                    U.set(t, l.not);
                    V.set(t, u0);
                    LINK.set(t, p);
                }
            }
        }
        // Do step L8 for all pairs (u,v) in TIMP(L) then return to L6.
        for (int p = L.TIMP, tcount = 0; tcount < L.TSIZE; p = NEXT.get(p), ++tcount) {
            final Literal u = U.get(p), v = V.get(p);
            if (tracing.contains(Trace.FIXING)) log.trace("  %s->%s|%s", L, u, v);
            makeParticipant(u.var);
            makeParticipant(v.var);
            if (!consider(u, v)) return false;
        }
        return true;
    }

    @Override
    void reactivate(Literal L) {
        for (int xi = neglit(L.var.id); xi >= poslit(L.var.id); --xi) {
            final Literal xlit = lit[xi];
            // Knuth insists (in the printed fascicle) that the downdating of TIMP should
            // happen in the reverse order of the updating, which would seem to argue for
            // traversing this linked list in reverse order. However, since each entry in
            // the TIMP list will point (via U and V) to two strictly other TIMP lists, it's
            // not clear why the order matters.

            buf.resetQuick();

            for (int p = xlit.TIMP, tcount = 0; tcount < xlit.TSIZE; p = NEXT.get(p), ++tcount)
                buf.add(p);
            for (int p = buf.size() - 1; p >= 0; --p) {
                final int k = buf.getQuick(p);
                ++U.get(k).not.TSIZE;
                ++V.get(k).not.TSIZE;
            }
        }
    }

    private void heuristicStep(float[] from, float[] to) {
        float sum, tsum, factor, sqfactor, afactor;
        final int N = nVariables - F;

        sum = 0;
        for (int i = 0; i < N; ++i) {
            final Variable v = VAR[i];
            sum += from[poslit(v.id)] + from[neglit(v.id)];
        }
        factor = 2f * N / sum;
        sqfactor = factor * factor;
        afactor = alpha * factor;
        for (int i = 0; i < N; ++i) {
            final Variable v = VAR[i];
            for (int li = poslit(v.id); li <= neglit(v.id); ++li) {
                final Literal l = lit[li];
                sum = 0;
                // for all u in BIMP[l] with u not fixed
                List<Literal> bimpl = l.BIMP;
                for (int j = 0; j < l.BSIZE; ++j) {
                    final Literal u = bimpl.get(j);
                    if (isfree(u)) {
                        sum += from[u.id];
                    }
                }
                tsum = 0;
                for (int p = l.TIMP, j = 0; j < l.TSIZE; p = NEXT.get(p), ++j) {
                    tsum += from[U.get(p).id] * from[V.get(p).id];
                }
                sum = 0.1f + sum * afactor + tsum * sqfactor;
                to[li] = Float.min(THETA, sum);
            }
        }
    }

    /**
     * Step X2: Compile rough heuristics.
     */
    @Override
    float[] computeHeuristics() {
        if (h[d] == null) {
            h[d] = new float[2 * nVariables + 2];
        }
        float[] hd = h[d];

        if (d <= 1) {
            Arrays.fill(hprime, 1);
            heuristicStep(hprime, hd);
            heuristicStep(hd, hprime);
            heuristicStep(hprime, hd);
            heuristicStep(hd, hprime);
            heuristicStep(hprime, hd);
        } else {
            heuristicStep(h[d - 1], hd);
        }
        return hd;
    }

    @Override
    protected boolean Perform72(final Literal l) {
        // @ A new breadth-first search is launched here, as we assert |looklit|
        // at truth level~|cs| and derive the ramifications of that assertion.
        //If, for example, |cs=50|, we will make |looklit| (and all other literals
        //that it implies) true at level~50, unless they're already true at
        //levels 52 or above.
        //
        //The consequences of |looklit| might include ``windfalls,'' which
        //are unfixed literals that are the only survivors of a clause whose
        //other literals have become false. Windfalls will be placed on the
        //|wstack|, which is cleared here.
        w = 0;
        G = E = F;
        W.clear();
        if (!propagate(l)) return false;  // Perform (62).
        while (G < E) {
            Literal L = R[G];
            ++G;
            // take account of (u, v) for all (u, v) in TIMP(L)
            for (int t = 0, p = L.TIMP; t < L.TSIZE; ++t, p = NEXT.getQuick(p)) {
                Literal u = U.get(p), v = V.get(p);
                if (tracing.contains(Trace.FIXING)) log.trace("  looking %s->%s|%s", L, u, v);
                Fixity fu = fixity(u), fv = fixity(v);
                if (fu == Fixity.FIXED_T || fv == Fixity.FIXED_T) continue;
                if (fu == Fixity.FIXED_F && fv == Fixity.FIXED_F) return false;
                if (fu == Fixity.FIXED_F && fv == Fixity.UNFIXED) {
                    if (!propagate(v)) return false;
                    W.push(v);
                } else if (fu == Fixity.UNFIXED && fv == Fixity.FIXED_F) {
                    if (!propagate(u)) return false;
                    W.push(u);
                } else {
                    assert fu == Fixity.UNFIXED && fv == Fixity.UNFIXED;
                    w += h[d][u.id] * h[d][v.id];
                }
            }
        }
        // generate new binary clauses (lbar_0 | w) for w in W. Knuth performs these steps in LIFO order; so do we.
        while (!W.isEmpty()) {
            Literal w = W.pop();
            if (tracing.contains(Trace.LOOKAHEAD)) log.trace("windfall %s->%s", l, w);
            appendToBimp(l, w);
            appendToBimp(w.not, l.not);
        }

        return true;
    }

    @Override
    protected boolean Perform73(Literal l) {
        G = E = F;
        if (!propagate(l)) return false;
        while (G < E) {
            Literal L = R[G];
            ++G;
            if (!timpForEach(L, (u, v) -> {
                if (tracing.contains(Trace.FIXING)) log.trace("  dlooking %s->%s|%s", L, u, v);
                Fixity fu = fixity(u), fv = fixity(v);
                if (fu == Fixity.FIXED_F && fv == Fixity.FIXED_F) return false;
                else if (fu == Fixity.FIXED_F && fv == Fixity.UNFIXED) return propagate(v);
                else if (fu == Fixity.UNFIXED && fv == Fixity.FIXED_F) return propagate(u);
                // the cases that remain: u and v are both unfixed, or at least one is fixed true: do nothing.
                return true;
            })) return false;
        }
        return true;
    }

    @Override
    void ResetFptr() {}

    @Override
    boolean wideClauses() { return false; }
}
