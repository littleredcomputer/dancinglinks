package net.littleredcomputer.knuth7;

import gnu.trove.list.array.TIntArrayList;
import gnu.trove.stack.TIntStack;
import gnu.trove.stack.array.TIntArrayStack;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.*;
import java.util.stream.Collectors;

public class SATAlgorithmL extends AbstractSATSolver {
    private static final Logger log = LogManager.getFormatterLogger();
    private static final int RT = 0x7ffffffe;
    private static final int NT = RT - 2;
    private static final int PT = RT - 2;

    // These next 4 arrays all grow in sync.
    private final TIntArrayList U = new TIntArrayList();
    private final TIntArrayList V = new TIntArrayList();
    private final TIntArrayList LINK = new TIntArrayList();
    private final TIntArrayList NEXT = new TIntArrayList();
    private final TIntArrayList FORCE = new TIntArrayList();
    private final TIntArrayList[] BIMP;
    private final int[] TIMP;  // ternary clause implications
    private final int[] VAR;
    private final int[] VAL;  // VAL[i] is the current contextual truth value of VAR[i]
    private final int[] DEC;
    private final int[] BACKF;
    private final int[] BACKI;
    private final int[] INX;  // INX[v] is the index of variable v in VAR
    private final int[] BRANCH;
    private final int[] TSIZE;  // TSIZE[l] is the length of the active segment of the TIMP array for literal l.
    private final int[] BSIZE;  // BSIZE[l] is the length of the active segment of the BIMP array for literal l.
    private final int[] IST;  // IST[l] is the ISTAMP value corresponding to the last extension of BIMP[l].
    private final int[] R;
    private final int[] CAND;  // candidates for algorithm X
    private final double[][] h;  // h[d][l] is the h-score of literal l at depth d
    private final double[] r;    // r[x] is the "rating" of variable x in step X3
    // Reading Knuth we might choose to implement ISTACK as a stack of pairs of ints. But that would require boxing.
    // Instead, we implement ISTACK as a pair of stacks of primitive ints.
    private final TIntStack ISTACKb = new TIntArrayStack();  // stack of literals
    private final TIntStack ISTACKs = new TIntArrayStack();  // stack of BIMP table size for corresponding literal above
    private int T = NT;  // truth degree (F6 7.2.2.2 p. 37)
    private int E = 0;  // literals R[k] are "nearly true" for G <= k < E.
    private int F = 0;
    private int G = 0;
    private int ISTAMP = 0;
    private int d = 0;  // current depth within search tree

    private enum Fixity {
        UNFIXED,
        FIXED_T,
        FIXED_F
    }

    SATAlgorithmL(SATProblem p) {
        super("L", p);
        final int nVariables = problem.nVariables();
        TIMP = new int[2*nVariables+2];
        BIMP = new TIntArrayList[2 * nVariables + 2];
        for (int l = 2; l < 2 * nVariables + 2; ++l) {
            BIMP[l] = new TIntArrayList();
            TIMP[l] = 0;
        }
        VAR = new int[nVariables];
        VAL = new int[nVariables+1];
        DEC = new int[nVariables];
        BACKF = new int[nVariables];
        BACKI = new int[nVariables];
        INX = new int[nVariables + 1];
        CAND = new int[nVariables];
        BRANCH = new int[nVariables];
        TSIZE = new int[2 * nVariables + 2];
        BSIZE = new int[2 * nVariables + 2];
        IST = new int[2 * nVariables + 2];
        R = new int[nVariables+1];  // stack to record the names of literals that have received values
        h = new double[nVariables][];
        h[0] = new double[2*nVariables+2];
        for (int i = 1; i <= nVariables; ++i) {
            h[0][2*i] = 1;
            h[0][2*i+1] = 1;
        }
        r = new double[nVariables + 1];

        Set<Integer> units = new HashSet<>();
        List<Set<Integer>> oBIMP = new ArrayList<>(2 * nVariables + 2);
        for (int i = 0; i < 2 * nVariables + 2; ++i) oBIMP.add(new HashSet<>());
        for (int i = 0; i < problem.nClauses(); ++i) {
            List<Integer> clause = problem.getClause(i);
            switch (clause.size()) {
                case 1: {
                    // Put it in the FORCE array, unless it is contradictory
                    final int u = clause.get(0);
                    if (units.contains(u ^ 1))
                        throw new IllegalArgumentException("Contradictory unit clauses involving variable " + (u >> 1) + " found");
                    units.add(u);
                    break;
                }
                case 2: {
                    // Put it in the BIMP.
                    final int u = clause.get(0), v = clause.get(1);
                    oBIMP.get(u ^ 1).add(v);
                    oBIMP.get(v ^ 1).add(u);
                    break;
                }
                case 3: {
                    // Put it in the TIMP
                    final int u = clause.get(0), v = clause.get(1), w = clause.get(2);

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

                    NEXT.add(TIMP[u ^ 1]);
                    NEXT.add(TIMP[v ^ 1]);
                    NEXT.add(TIMP[w ^ 1]);

                    TIMP[u ^ 1] = z;
                    TIMP[v ^ 1] = z + 1;
                    TIMP[w ^ 1] = z + 2;

                    ++TSIZE[u ^ 1];
                    ++TSIZE[v ^ 1];
                    ++TSIZE[w ^ 1];

                    break;
                }
                default:
                    throw new IllegalArgumentException("Algorithm L can only cope with 3SAT at the moment " + clause.size());
            }
        }
        for (int l = 2; l < 2 * nVariables + 2; ++l) {
            BIMP[l].addAll(oBIMP.get(l));
            BSIZE[l] = BIMP[l].size();
        }
        FORCE.addAll(units);
        for (int k = 0; k < nVariables; ++k) {
            VAR[k] = k + 1;
            INX[k + 1] = k;
        }
    }

    /**
     * Propagate the literal l through all of the binary clauses using the BIMP table.
     * If a conflict is at any point, the propagation is abandoned early and false is
     * returned.
     */
    private boolean propagate(int l) {
        int H = E;
        if (!takeAccountOf(l)) {
            return false;
        }
        for (; H < E; ++H) {
            TIntArrayList bimpl = BIMP[R[H]];
            for (int i = 0; i < BSIZE[R[H]]; ++i) {
                if (!takeAccountOf(bimpl.get(i))) return false;
            }
        }
        return true;
    }

    /* True if BIMP[b] contains l. */
    private boolean bimpContains(int b, int l) {
        TIntArrayList bimpl = BIMP[b];
        for (int i = 0; i < BSIZE[b]; ++i) if (bimpl.get(i) == l) return true;
        return false;
    }

    /* Append l to BIMP[b], allowing for an undo in the future. */
    private void appendToBimp(int b, int l) {
        final int bsize = BSIZE[b];
        if (IST[b] != ISTAMP) {
            IST[b] = ISTAMP;
            ISTACKb.push(b);
            ISTACKs.push(bsize);
        }
        TIntArrayList bimp = BIMP[b];
        if (bimp.size() > bsize) bimp.set(bsize, l);
        else if (bimp.size() == bsize) bimp.add(l);
        else throw new IllegalStateException("bimp size invariant violation");
        ++BSIZE[b];
    }

    private static int dl(int literal) { return SATProblem.decodeLiteral(literal); }
    /**
     * Implements steps L8 and L9 of Algorithm L. Returns false if the next step is CONFLICT.
     */
    private boolean consider(int u, int v) {
        if (log.isTraceEnabled()) log.trace("consider %d∨%d\n", dl(u), dl(v));
        // STEP L8: Consider u ∨ v
        Fixity fu = fixity(u);
        Fixity fv = fixity(v);

        if (fu == Fixity.FIXED_T || fv == Fixity.FIXED_T) return true;
        else if (fu == Fixity.FIXED_F && fv == Fixity.FIXED_F) return false;
        else if (fu == Fixity.FIXED_F && fv == Fixity.UNFIXED) return propagate(v);
        else if (fv == Fixity.FIXED_F && fu == Fixity.UNFIXED) return propagate(u);
        // STEP L9: Exploit u || v.
        if (bimpContains(u ^ 1, v ^ 1)) return propagate(u);
        else if (bimpContains(u ^ 1, v)) return true;
        else if (bimpContains(v ^ 1, u ^ 1)) return propagate(v);
        // Append v to BIMP(¬u), u to BIMP(¬v).
        appendToBimp(u ^ 1, v);
        appendToBimp(v ^ 1, u);
        return true;
    }

    /* Returns the fixity of l in the context T */
    private Fixity fixity(int l) {
        int val = VAL[l >> 1];
        if (val < T) return Fixity.UNFIXED;
        return (val & 1) == (l & 1) ? Fixity.FIXED_T : Fixity.FIXED_F;
    }

    /**
     * Implements equation (62) of 7.2.2.2. Returns false if the next step is CONFLICT.
     */
    private boolean takeAccountOf(int l) {
        switch (fixity(l)) {
            case FIXED_T: {
                break;
            }
            case FIXED_F: {
                return /* conflict */ false;
            }
            case UNFIXED:
                VAL[l >> 1] = T + (l & 1);
                R[E] = l;
                ++E;
        }
        return true;
    }

    private String timpToString(int l) {
        StringBuilder sb = new StringBuilder();
        sb.append(String.format("  %3d: ", dl(l)));
        for (int i = 0, p = TIMP[l]; i < TSIZE[l]; i++, p = NEXT.get(p)) {
            sb.append(dl(U.get(p))).append(':').append(dl(V.get(p))).append(' ');
        }
        return sb.toString();
    }

    private void print() {
        final int nVariables = problem.nVariables();
        log.trace("BIMP tables:");
        for (int l = 2; l <= 2*nVariables+1; ++l) {
            if (BSIZE[l] < 0) throw new IllegalStateException(String.format("bad BIMP at %d (%d): %d", l, dl(l), BSIZE[l]));
            if (BSIZE[l] > 0) {
                TIntArrayList b = BIMP[l];
                StringBuilder sb = new StringBuilder();
                sb.append(String.format("  %3d: ", dl(l)));
                for (int i = 0; i < BSIZE[l]; ++i) sb.append(dl(b.get(i))).append(' ');
                log.trace(sb.toString());
            }
        }
        log.trace("TIMP tables:");
        for (int l = 2; l <= 2*nVariables+1; ++l) {
            if (TSIZE[l] > 0) {
                log.trace(timpToString(l));
            }
        }
        log.trace("E=%d F=%d G=%d VAR %s VAL %s\n", E, F, G, Arrays.toString(VAR), Arrays.toString(VAL));
    }

    private String stateToString() {
        return Arrays.stream(VAL).skip(1).mapToObj(i -> i == 0 ? "\u00b7" : (i&1) == 0 ? "1" : "0").collect(Collectors.joining());
    }

    @Override
    public Optional<boolean[]> solve() {
        start();
        final int nVariables = problem.nVariables();
        int CONFLICT = 0;
        int N = VAR.length;
        int state = 2;
        int l = 0;
        int L = 0;

        STEP:
        while (true) {
            ++stepCount;
            if (stepCount % logCheckSteps == 0) {
                maybeReportProgress(this::stateToString);
            }
            if (log.isTraceEnabled()) log.trace(">>>> step %d state %d", stepCount, state);
            switch (state) {
                case 2:  // New node.
                    if (FORCE.size() > 0) {
                        state = 5;
                        continue;
                    }
                    // Step X1:  Satisfied?
                    if (F == nVariables) {
                        boolean sat[] = new boolean[nVariables];
                        for (int i = 1; i <= nVariables; ++i) sat[i-1] = (VAL[i] & 1) == 0;
                        return Optional.of(sat);
                    }
                    // X();
                    // Go to state 15 if alg. X has discovered a conflict.
                    if (FORCE.size() == 0) {
                        log.trace("Not running algorithm X");
                    }
                    BRANCH[d] = -1;
                case 3: {  // Choose l.
                    // If we had algorithm X, we could make a smart choice.
                    // Algorithm X can also reply "0".  For now, we're going
                    // to just pick the first literal that's free.
                    if (0 >= N) throw new IllegalStateException("Can't find a free var in step 3");
                    l = 2*VAR[0]+1; // trivial heuristic: deny the first free variable
                    if (l == 0) {
                        ++d;
                        state = 2;
                        continue;
                    }
                    DEC[d] = l;
                    BACKF[d] = F;
                    BACKI[d] = ISTACKb.size();
                    BRANCH[d] = 0;
                }
                case 4:  // Try l.

                    if (log.isTraceEnabled()) print();
                    if (log.isTraceEnabled()) log.trace("d=%d: Trying %d", d, dl(l));
                    // u = 1;            // FIXME: is u just the size of the FORCE array? Can we eliminate that variable?
                    // FORCE.add(l);
                    // Not quite! we can get here from step 14 which can be a consequence of CONFLICT in step 5 via step 11. So,
                    // while we can still get rid of u, we need to clear this array here.
                    FORCE.resetQuick();
                    FORCE.add(l);
                    // FORCE.set(0, l);  // FIXME: Can this step be folded into step 3, and the scope of l thereby reduced?
                case 5:  // Accept near truths.
                    log.trace("Accepting near-truths");
                    T = NT;
                    G = E = F;
                    ++ISTAMP;
                    CONFLICT = 11;
                    // Perform the binary propagation routine (62) for all the literals in FORCE
                    for (int i = 0; i < FORCE.size(); ++i) { // int f : FORCE) { removed since allocation is done
                        if (!propagate(FORCE.get(i))) {
                            state = CONFLICT;
                            continue STEP;
                        }
                    }
                    FORCE.resetQuick();

                case 6:  // Choose a nearly true l.
                    if (log.isTraceEnabled()) log.trace("Choose a nearly true l. G=%d, E=%d\n", G, E);
                    if (G == E) {
                        state = 10;
                        continue;
                    }
                    L = R[G];
                    ++G;
                    if (log.isTraceEnabled()) log.trace("Chose %d. Now G=%d", dl(L), G);
                case 7: {  // Promote L to real truth.
                    if (log.isTraceEnabled()) log.trace("** Promote %d to real truth\n", dl(L));
                    int X = L >> 1;
                    VAL[X] = RT + (L & 1);
                    // Remove variable X from the free list and from all TIMP pairs (ex. 137).
                    N = nVariables - G;
                    int x = VAR[N];
                    int j = INX[X];
                    VAR[j] = x;
                    INX[x] = j;
                    VAR[N] = X;
                    INX[X] = N;
                    for (int l0 = 2 * X; l0 <= 2 * X + 1; ++l0) {
                        // System.out.printf("purging %d\n", dl(l0));
                        for (int p = TIMP[l0], tcount = 0; tcount < TSIZE[l0]; p = NEXT.get(p), ++tcount) {
                            int u0 = U.get(p);
                            int v = V.get(p);
                            int pp = LINK.get(p);
                            int ppp = LINK.get(pp);
                            int s = TSIZE[u0 ^ 1] - 1;
                            TSIZE[u0 ^ 1] = s;
                            int t = TIMP[u0 ^ 1];
                            for (int i = 0; i < s; ++i) t = NEXT.get(t);
                            if (pp != t) {
                                int uu = U.get(t);
                                int vv = V.get(t);
                                int q = LINK.get(t);
                                int qq = LINK.get(q);
                                LINK.set(qq, pp);
                                LINK.set(p, t);
                                U.set(pp, uu);
                                V.set(pp, vv);
                                LINK.set(pp, q);
                                U.set(t, v);
                                V.set(t, l0 ^ 1);
                                LINK.set(t, ppp);

                                // NOT IN KNUTH: reset pp, ppp.
                                pp = t;
                                // END NOT IN KNUTH
                            }
                            // Then set...
                            s = TSIZE[v ^ 1] - 1;
                            TSIZE[v ^ 1] = s;
                            t = TIMP[v ^ 1];
                            for (int i = 0; i < s; ++i) t = NEXT.get(t);
                            if (ppp != t) {  // swap pairs by setting
                                int uu = U.get(t);
                                int vv = V.get(t);
                                int q = LINK.get(t);
                                int qq = LINK.get(q);
                                LINK.set(qq, ppp);
                                LINK.set(pp, t);
                                U.set(ppp, uu);
                                V.set(ppp, vv);
                                LINK.set(ppp, q);
                                U.set(t, l0 ^ 1);
                                V.set(t, u0);
                                LINK.set(t, p);
                            }
                        }
                    }

                    // Do step L8 for all pairs (u,v) in TIMP(L) then return to L6.
                    for (int p = TIMP[L], tcount = 0; tcount < TSIZE[L]; p = NEXT.get(p), ++tcount) {
                        boolean conflict = !consider(U.get(p), V.get(p));
                        if (conflict) {
                            state = CONFLICT;
                            continue STEP;
                        }
                    }
                    state = 6;
                    continue;
                }
                /* Steps 8 and 9 are in the method consider(). */
                case 10:  // Accept real truths.
                    if (log.isTraceEnabled()) log.trace("state 10 E=%d F=%d BRANCH[%d]=%d",E,F,d,BRANCH[d]);
                    F = E;
                    if (BRANCH[d] >= 0) {
                        ++d;
                        state = 2;
                        continue;
                    }
                    state = d > 0 ? 3 : 2;
                    continue;
                case 11:  // Unfix near truths.
                    while (E > G) {
                        --E;
                        if (log.isTraceEnabled()) log.trace("Retracting %d", dl(R[E]));
                        VAL[R[E] >> 1] = 0;
                    }
                case 12:  // Unfix real truths.
                    while (E > F) {
                        --E;
                        int X = R[E]>>1;
                        // reactivate the TIMP pairs that involve X and restore X to the free list (ex. 137)
                        for (int l0 = 2*X + 1; l0 >= 2*X; --l0) {
                            if (log.isTraceEnabled()) log.trace("Reactivating %d\n",dl(l0));
                            // Knuth insists (in the printed fascicle) that the downdating of TIMP should
                            // happen in the reverse order of the updating, which would seem to argue for
                            // traversing this linked list in reverse order. However, since each entry in
                            // the TIMP list will point (via U and V) to two strictly other TIMP lists, it's
                            // not clear why the order matters.
                            for (int p = TIMP[l0], tcount = 0; tcount < TSIZE[l0]; p = NEXT.get(p), ++tcount) {
                                int u0 = U.get(p);
                                int v = V.get(p);
                                ++TSIZE[v ^ 1];
                                ++TSIZE[u0 ^ 1];
                            }
                        }
                        VAL[X] = 0;
                    }
                case 13:  // Downdate BIMPs
                    if (BRANCH[d] >= 0) {
                        while (ISTACKb.size() > BACKI[d]) {
                            BSIZE[ISTACKb.pop()] = ISTACKs.pop();
                        }
                    }
                case 14:  // Try again?
                    if (BRANCH[d] == 0) {
                        l = DEC[d];
                        DEC[d] = l = (l ^ 1);
                        BRANCH[d] = 1;
                        if (log.isTraceEnabled()) log.trace("d=%d. That didn't work, trying %d", d, dl(l));
                        state = 4;
                        continue;
                    }
                case 15:  // Backtrack.
                    if (log.isTraceEnabled()) log.trace("Backtracking from level %d", d);
                    if (d == 0) {
                        log.trace("UNSAT");
                        return Optional.empty();
                    }
                    --d;
                    E = F;
                    F = BACKF[d];
                    state = 12;
                    continue;
                default:
                    throw new IllegalStateException("Internal error: illegal state " + state);
            }
        }
    }

    /**
     * Knuth's Algorithm X, which is used to gather information guiding the selection of literals
     * in Algorithm L.
     */
    public void X() {
        final int nVariables = problem.nVariables();
        final int N = nVariables - F;
        double[] hd = h[d];
        final double alpha = 3.5;
        final double THETA = 20.0;
        final int C0 = 30, C1 = 600;  // See Ex. 148

        int nCycles = 5;

        // This is the BIMP/TIMP form.
        System.out.printf(" h[d]: %s\n", Arrays.toString(hd));

        // Step X1 is performed before this routine is called.
        // Step X2: Compile rough heuristics.
        for (int k = 0; k < nCycles; ++k) {
            double hAve = 0.0;
            for (int i = 1; i <= nVariables; ++i) {
                if (INX[i] < N) {
                    hAve += hd[2 * i] + hd[2 * i + 1];
                }
            }
            hAve /= 2.0 * nVariables;
            final double hAve2 = hAve * hAve;
            double[] hprime = new double[hd.length];
            for (int i = 1; i <= nVariables; ++i) {
                if (INX[i] < N) {
                    for (int l = 2*i; l <= 2*i+1; ++l) {
                        // update hd[l]
                        double hp = 0.1;
                        // for all u in BIMP[l] with u not fixed
                        TIntArrayList bimpl = BIMP[l];
                        double hs = 0;
                        for (int j = 0; j < BSIZE[l]; ++j) hs += hd[bimpl.get(j)] / hAve;
                        hp += alpha * hs;
                        for (int p = TIMP[l], j = 0; j < TSIZE[l]; p = NEXT.get(p), ++j) {
                            hp += hd[U.get(p)] * hd[V.get(p)] / hAve2;
                        }
                        hprime[l] = hp > THETA ? THETA : hp;
                    }
                }
            }
            System.arraycopy(hprime, 2, hd, 2, 2*nVariables);
        }
        System.out.printf(" h0: %s\n", Arrays.toString(h[0]));
        System.out.printf(" nc: %d\n", problem.nClauses());
        // Step X3: Preselect candidates.
        // XXX: how many variables are "participants"?
        int C = 0;  // for now, we don't know of any.

        if (C == 0) {
            C = N;
            System.arraycopy(VAR, 0, CAND, 0, C);
            // "Terminate happily, however, if all free clauses are satisfied...."
            // From Ex. 152:
            //  "Indeed, the absence of free participants means that the fixed-true
            //   literals form an autarky. If TSIZE(l) is nonzero for any free literal
            //   l, some clause is unsatisfied. Otherwise all clauses are satisfied
            //   unless some free l has an unfixed literal lʹ ∈ BIMP(l)."
            boolean sat = true;
            OUTER: for (int v : CAND) {  // XXX allocates an iterator? often enough to worry about?
                for (int l = 2*v; l <= 2*v+1; ++l) {
                    // l is a free literal since v is a free variable.
                    if (TSIZE[l] > 0) {
                        sat = false;
                        break OUTER;
                    }
                    TIntArrayList bimpl = BIMP[l];
                    for (int j = 0; j < BSIZE[l]; ++j) {
                        if (fixity(bimpl.get(j)) == Fixity.UNFIXED) {
                            sat = false;
                            break OUTER;
                        }
                    }
                }
            }
            if (sat) throw new IllegalStateException("X found SAT!");
        } else {
            throw new IllegalStateException("Don't know how to proceed yet");
        }

        // Give each variable x in CAND the rating r(x) = h(x)h(¬x)
        double r_sum = 0.;
        for (int v : CAND) {
            r[v] = hd[2*v] * hd[2*v+1];
            r_sum += r[v];
        }
        double r_mean = r_sum / CAND.length;

        final double C_max = d == 0 ? C1 : Integer.max(C0, C1/d);  // Eq. (66)

        log.trace("mean rating %g", r_mean);
        log.trace("C_max = %g", C_max);
        // While C > 2 C_max, delete all elements of CAND whose rating
        // exceeds the mean rating; but terminate the loop if no elements are
        // actually deleted.

        // Finally, if C > C_max, reduce C to C_max by retaining only top-ranked
        // candidates.

        // X4 [Nest the can didates.]

        // "Construct a lookahead forest, represented in LL[j] and LO[j] for 0 ≤ j < S
        // and by PARENT pointers (see ex. 155).

        // X5 [Prepare to explore.]
        // X6 [Choose l for lookahead.]
        // X7 [Move to next.]
        // X8 [Compute sharper heuristic.]
        // X9 [Exploit an autarky.]
        // X10 [Optionally look deeper.]
        // X11 [Exploit unnecessary assignments.]
        // X12 [Force l.] (this is a subroutine...)
        // X13 [Recover from conflict.]

    }
}
