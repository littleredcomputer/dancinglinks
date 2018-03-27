package net.littleredcomputer.knuth7;

import gnu.trove.list.TIntList;
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

    private final List<TIntArrayList> BIMP;
    private final TIntArrayList TIMP;
    private final int[] VAR;
    private final int[] VAL;
    private final int[] DEC;
    private final int[] BACKF;
    private final int[] BACKI;
    private final int[] INX;
    private final int[] BRANCH;
    private final int[] TSIZE;  // TSIZE[l] is the length of the active segment of the TIMP array for literal l.
    private final int[] BSIZE;  // BSIZE[l] is the length of the active segment of the BIMP array for literal l.
    private final int[] IST;  // IST[l] is the ISTAMP value corresponding to the last extension of BIMP[l].
    private final int[] R;
    // Reading Knuth we might choose to implement ISTACK as a stack of pairs of ints. But that would require boxing.
    // Instead, we implement ISTACK as a pair of stacks of primitive ints.
    private final TIntStack ISTACKb = new TIntArrayStack();  // stack of literals
    private final TIntStack ISTACKs = new TIntArrayStack();  // stack of BIMP table size for corresponding literal above
    private int T = NT;  // truth degree (F6 7.2.2.2 p. 37)
    private int E = 0;  // literals R[k] are "nearly true" for G <= k < E.
    private int F = 0;
    private int G = 0;
    private int ISTAMP = 0;

    private enum Fixity {
        UNFIXED,
        FIXED_T,
        FIXED_F
    }

    SATAlgorithmL(SATProblem p) {
        super("L", p);
        final int nVariables = problem.nVariables();
        TIMP = new TIntArrayList(2 * nVariables + 2);
        BIMP = new ArrayList<>(2 * nVariables + 2);
        for (int i = 0; i < 2 * nVariables + 2; ++i) BIMP.add(new TIntArrayList());
        for (int i = 0; i < 2 * nVariables + 2; ++i) TIMP.add(0);
        VAR = new int[nVariables];
        VAL = new int[nVariables+1];
        DEC = new int[nVariables];
        BACKF = new int[nVariables];
        BACKI = new int[nVariables];
        INX = new int[nVariables + 1];
        BRANCH = new int[nVariables];
        TSIZE = new int[2 * nVariables + 2];
        BSIZE = new int[2 * nVariables + 2];
        IST = new int[2 * nVariables + 2];
        R = new int[nVariables+1];  // stack to record the names of literals that have received values


        // XXX consider moving tableau creation to the constructor
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

                    NEXT.add(TIMP.get(u ^ 1));
                    NEXT.add(TIMP.get(v ^ 1));
                    NEXT.add(TIMP.get(w ^ 1));

                    TIMP.set(u ^ 1, z);
                    TIMP.set(v ^ 1, z + 1);
                    TIMP.set(w ^ 1, z + 2);

                    ++TSIZE[u ^ 1];
                    ++TSIZE[v ^ 1];
                    ++TSIZE[w ^ 1];

                    break;
                }
                default:
                    throw new IllegalArgumentException("Algorithm L can only cope with 3SAT at the moment " + clause.size());
            }
        }
        for (int i = 0; i < 2 * nVariables + 2; ++i) BIMP.get(i).addAll(oBIMP.get(i));
        Arrays.setAll(BSIZE, i -> BIMP.get(i).size());
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
            TIntList bimpl = BIMP.get(R[H]);
            for (int i = 0; i < BSIZE[R[H]]; ++i) {
                if (!takeAccountOf(bimpl.get(i))) return false;
            }
        }
        return true;
    }

    /* True if BIMP[b] contains l. */
    private boolean bimpContains(int b, int l) {
        TIntList bimpl = BIMP.get(b);
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
        TIntList bimp = BIMP.get(b);
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
        for (int i = 0, p = TIMP.get(l); i < TSIZE[l]; i++, p = NEXT.get(p)) {
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
                TIntList b = BIMP.get(l);
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
        int N = VAR.length;
        int d = 0;
        int CONFLICT = 0;
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
                    X();
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
                        for (int p = TIMP.get(l0), tcount = 0; tcount < TSIZE[l0]; p = NEXT.get(p), ++tcount) {
                            int u0 = U.get(p);
                            int v = V.get(p);
                            int pp = LINK.get(p);
                            int ppp = LINK.get(pp);
                            int s = TSIZE[u0 ^ 1] - 1;
                            TSIZE[u0 ^ 1] = s;
                            int t = TIMP.get(u0 ^ 1);
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
                            t = TIMP.get(v ^ 1);
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
                    for (int p = TIMP.get(L), tcount = 0; tcount < TSIZE[L]; p = NEXT.get(p), ++tcount) {
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
                            for (int p = TIMP.get(l0), tcount = 0; tcount < TSIZE[l0]; p = NEXT.get(p), ++tcount) {
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
    private void X() {
        int N = problem.nVariables() - F;
        // Use (65) to compute a rough score h(l) for each free literal l.


    }
}
