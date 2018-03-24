package net.littleredcomputer.knuth7;

import com.google.common.collect.Lists;
import javafx.util.Pair;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.*;
import java.util.function.IntPredicate;
import java.util.stream.Collectors;

public class SATAlgorithmL extends AbstractSATSolver {
    private static final Logger log = LogManager.getFormatterLogger();
    private static int RT = 0x7ffffffe;
    private static int NT = RT - 2;
    private static int PT = RT - 2;

    // These next 4 arrays all grow in sync.
    private final List<Integer> U = new ArrayList<>();
    private final List<Integer> V = new ArrayList<>();
    private final List<Integer> LINK = new ArrayList<>();
    private final List<Integer> NEXT = new ArrayList<>();
    private final List<List<Integer>> BIMP;
    private final List<Integer> TIMP;
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
    private final Stack<Pair<Integer, Integer>> ISTACK = new Stack<>();
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
        TIMP = new ArrayList<>(2 * nVariables + 2);
        BIMP = new ArrayList<>(2 * nVariables + 2);
        for (int i = 0; i < 2 * nVariables + 2; ++i) BIMP.add(new ArrayList<>());
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
    }

    /**
     * Propagate the literal l through all of the binary clauses using the BIMP table.
     * If a conflict is at any point, the propagation is abandoned early and false is
     * returned.
     */
    private boolean propagate(int l) {
        log.trace("propagate %d", SATProblem.decodeLiteral(l));
        int H = E;
        if (!takeAccountOf(l)) {
            log.trace("immediate conflict");
            return false;
        }
        for (; H < E; ++H) {
            log.trace("extra propagation for %d", SATProblem.decodeLiteral(R[H]));
            if (!bimpForEach(R[H], this::takeAccountOf)) {
                log.trace("conflict at R[H]=%d", SATProblem.decodeLiteral(R[H]));
                return false;
            }
        }
        return true;
    }

    /* Calls f on all the elements of the BIMP list of literal l. If at any point f returns false,
     * the loop is abandoned and false is returned.
     */
    private boolean bimpForEach(int l, IntPredicate f) {
        List<Integer> bimpl = BIMP.get(l);
        for (int i = 0; i < BSIZE[l]; ++i) {
            if (!f.test(bimpl.get(i))) return false;
        }
        return true;
    }

    /* True if BIMP[b] contains l. */
    private boolean bimpContains(int b, int l) {
        return !bimpForEach(b, i -> i != l);
    }

    /* Append l to BIMP[b], allowing for an undo in the future. */
    private void appendToBimp(int b, int l) {
        if (IST[b] != ISTAMP) {
            IST[b] = ISTAMP;
            ISTACK.push(new Pair<>(b, BSIZE[b])); // XXX allocation
        }
        BIMP.get(b).add(l);
        ++BSIZE[b];
    }

    // TODO: from the bottom up, implement an escape discipline for the CONFLICT cases in the subroutines.

    private static int dl(int literal) { return SATProblem.decodeLiteral(literal); }
    /**
     * Implements steps L8 and L9 of Algorithm L. Returns false if the next step is CONFLICT.
     */
    private boolean consider(int u, int v) {
        log.trace("consider %d∨%d\n", dl(u), dl(v));
        // STEP L8: Consider u ∨ v
        Fixity fu = fixity(u);
        Fixity fv = fixity(v);

        if (fu == Fixity.FIXED_T || fv == Fixity.FIXED_T) {
            log.trace("... %s, %s: so doing nothing\n", fu.toString(), fv.toString());
            return true;
        }
        else if (fu == Fixity.FIXED_F && fv == Fixity.FIXED_F) {
            log.trace("...both fixed false: conflict");
            return false;
        }
        else if (fu == Fixity.FIXED_F && fv == Fixity.UNFIXED) {
            log.trace("... %d was fixed false, so propagating unfixed %d\n", dl(u), dl(v));
            return propagate(v);
        } else if (fv == Fixity.FIXED_F && fu == Fixity.UNFIXED) {
            log.trace("... %d was fixed false, so propagating unfixed %d\n", dl(v), dl(u));
            return propagate(u);
        }
        log.trace("Exploiting %d∨%d\n", dl(u), dl(v));
        // STEP L9: Exploit u || v.
        if (bimpContains(u ^ 1, v ^ 1)) {
            log.trace("...BIMP[%d] contains %d, so propagating %d\n", dl(u^1), dl(v^1), dl(u));
            return propagate(u);
        }
        else if (bimpContains(u ^ 1, v)) {
            log.trace("...BIMP[%d] contains %d, so doing nothing\n", dl(u^1), dl(v));
            return true;
        }
        else if (bimpContains(v ^ 1, u ^ 1)) {
            log.trace("...BIMP[%d] contains %d, so propagating %d\n", dl(v^1), dl(u^1), dl(v));
            return propagate(v);
        }
        // Append v to BIMP(¬u), u to BIMP(¬v).
        log.trace("...Appending %d to BIMP[%d], %d to BIMP[%d]\n", dl(v), dl(u^1), dl(u), dl(v^1));
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
                log.trace("takeAccountOf(%d) finds that it's FIXED_T", dl(l));
                break;
            }
            case FIXED_F: {
                log.trace("takeAccountOf(%d) finds that it's FIXED_F and therefore in conflict", dl(l));
                return /* conflict */ false;
            }
            case UNFIXED:
                log.trace("takeAccountOf asserting %d", dl(l));
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
//        sb.append("          ");
//        for (int i = 0, p = TIMP.get(l); i < TSIZE[l]; i++, p = NEXT.get(p)) {
//            sb.append('[').append(dl(U.get(LINK.get(p)))).append(':').append(dl(V.get(LINK.get(p)))).append('@').append(LINK.get(p)).append(' ');
//            sb.append(dl(U.get(LINK.get(LINK.get(p))))).append(':').append(dl(V.get(LINK.get(LINK.get(p))))).append('@').append(LINK.get(LINK.get(p))).append(' ');
//            sb.append(dl(U.get(LINK.get(LINK.get(LINK.get(p)))))).append(':').append(dl(V.get(LINK.get(LINK.get(LINK.get(p)))))).append('@').append(LINK.get(LINK.get(LINK.get(p)))).append("] ");
//        }
        return sb.toString();
    }

    private void print() {
        final int nVariables = problem.nVariables();
        System.out.printf("BIMP tables:\n");
        for (int l = 2; l <= 2*nVariables+1; ++l) {
            if (BSIZE[l] < 0) throw new IllegalStateException(String.format("bad BIMP at %d (%d): %d", l, dl(l), BSIZE[l]));
            if (BSIZE[l] > 0) {
                List<Integer> b = BIMP.get(l);
                System.out.printf("  %3d: ", dl(l));
                for (int i = 0; i < BSIZE[l]; ++i) System.out.printf("%d ", dl(b.get(i)));
                System.out.println();
            }
        }
        System.out.println("TIMP tables:\n");
        for (int l = 2; l <= 2*nVariables+1; ++l) {
            if (TSIZE[l] > 0) {
                System.out.println(timpToString(l));
            }
        }
        System.out.printf("E=%d F=%d G=%d VAR %s VAL %s\n", E, F, G, Arrays.toString(VAR), Arrays.toString(VAL));
//        System.out.println("INX " + Arrays.toString(INX));
    }

    @Override
    public Optional<boolean[]> solve() {
        final int nVariables = problem.nVariables();
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
        List<Integer> FORCE = Lists.newArrayList(units);
        int N = VAR.length;
        //int u = FORCE.size();
        for (int k = 0; k < nVariables; ++k) {
            VAR[k] = k + 1;
            INX[k + 1] = k;
        }
        int d = 0;
        int CONFLICT = 0;

        int state = 2;
        int l = 0;
        int L = 0;

        System.out.printf("    U: %s\n", U);
        System.out.printf("    V: %s\n", V);
        System.out.printf(" NEXT: %s\n", NEXT);
        System.out.printf(" LINK: %s\n", LINK);
        System.out.printf(" TIMP: %s\n", TIMP);
        System.out.printf("TSIZE: %s\n", Arrays.toString(TSIZE));

        System.out.println("clauses:");
        for (int i = 0; i < problem.nClauses(); ++i) {
            List<Integer> c = problem.getClause(i);
            for (int l0 : c) System.out.printf("%d ", dl(l0));
            System.out.print("   ");
        }
        System.out.println();

        STEP:
        while (true) {
            ++stepCount;
            if (stepCount % logCheckSteps == 0) {
                maybeReportProgress(() -> Arrays.stream(VAL).skip(1).mapToObj(i -> i == 0 ? "." : (i&1) == 0 ? "1" : "0").collect(Collectors.joining()));
            }

            // if (stepCount > 1000) throw new IllegalStateException("done");
            // print();
            System.out.printf(">>>> state %d   (this is step %d)\n", state, stepCount);
            switch (state) {
                case 0:
                case 1:
                    throw new IllegalStateException("Internal error: illegal state " + state);
                case 2:  // New node.
                    if (FORCE.size() > 0) {
                        state = 5;
                        continue;
                    }
                    // Step X1:  Satisfied?
                    if (F == nVariables) {
                        System.out.printf("returning because SAT\n");
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    boolean sat[] = new boolean[nVariables];
                        for (int i = 1; i <= nVariables; ++i) sat[i-1] = (VAL[i] & 1) == 0;
                        return Optional.of(sat);
                    }
                    // Go to state 15 if alg. X has discovered a conflict.
                    if (FORCE.size() == 0) {
                        log.warn("Not running algorithm X");
                    }
                    BRANCH[d] = -1;
                case 3: {  // Choose l.
                    // If we had algorithm X, we could make a smart choice.
                    // Algorithm X can also reply "0".  For now, we're going
                    // to just pick the first literal that's free.

                    // Where we left off: that dumb pick above is picking the same literal each time.

                    if (0 >= N) throw new IllegalStateException("Can't find a free var in step 3");
                    l = 2*VAR[0]+1; // trivial heuristic: deny the first free variable
                    if (l == 0) {
                        ++d;
                        state = 2;
                        continue;
                    }
                    DEC[d] = l;
                    BACKF[d] = F;
                    BACKI[d] = ISTACK.size();
                    BRANCH[d] = 0;
                }
                case 4:  // Try l.
                    log.trace("d=%d. Trying %d", d, dl(l));
                    // u = 1;            // FIXME: is u just the size of the FORCE array? Can we eliminate that variable?
                    // FORCE.add(l);
                    // Not quite! we can get here from step 14 which can be a consequence of CONFLICT in step 5 via step 11. So,
                    // while we can still get rid of u, we need to clear this array here.
                    FORCE.clear();
                    FORCE.add(l);
                    // FORCE.set(0, l);  // FIXME: Can this step be folded into step 3, and the scope of l thereby reduced?
                case 5:  // Accept near truths.
                    log.trace("Accepting near-truths");
                    T = NT;
                    G = E = F;
                    ++ISTAMP;
                    CONFLICT = 11;
                    // Perform the binary propagation routine (62) for all the literals in FORCE
                    for (int f : FORCE) {
                        if (!propagate(f)) {
                            state = CONFLICT;
                            continue STEP;
                        }
                    }
                    FORCE.clear();

                case 6:  // Choose a nearly true l.
                    log.trace("Choose a nearly true l. G=%d, E=%d\n", G, E);
                    if (G == E) {
                        state = 10;
                        continue;
                    }
                    L = R[G];
                    ++G;
                    log.trace("Chose %d. Now G=%d", dl(L), G);
                case 7: {  // Promote L to real truth.
                    log.trace("** Promote %d to real truth\n", dl(L));
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
                            // System.out.printf("looking at pair %d:%d\n", dl(u0), dl(v));
                            // System.out.printf("  associated pair #1: %d:%d\n", dl(U.get(pp)), dl(V.get(pp)));
                            // System.out.printf("  associated pair #2: %d:%d\n", dl(U.get(ppp)), dl(V.get(ppp)));
                            // System.out.printf("The cycle is %d-%d-%d-%d\n", p, pp, ppp, LINK.get(ppp));
                            // System.out.printf("BEFORE is %s\n", timpToString(u0^1));
                            int s = TSIZE[u0 ^ 1] - 1;
                            TSIZE[u0 ^ 1] = s;
                            int t = TIMP.get(u0 ^ 1);
                            for (int i = 0; i < s; ++i) t = NEXT.get(t); // XXX i = 1 or 0 here?


                            // System.out.printf("pair s=%d of TIMP(%d) is %d:%d @%d\n", s, dl(u0^1), dl(U.get(t)), dl(V.get(t)), t);
                            // System.out.printf("The first t-cycle is %d-%d-%d-%d\n", t, LINK.get(t), LINK.get(LINK.get(t)), LINK.get(LINK.get(LINK.get(t))));
                            if (pp != t) {
//                                System.out.printf("swapping pairs A %d:%d @%d <-> %d:%d @%d\n", dl(U.get(t)),
//                                        dl(V.get(t)), t,
//                                        dl(U.get(pp)),
//                                        dl(V.get(pp)),
//                                        pp);
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

                                // NOT IN KNUTH: reset pp, ppp.  Initially this was below the following closing brace, but it looks
                                // like it could be here, since the assignments to pp, ppp are otherwise unmolested
                                pp = LINK.get(p);
                                ppp = LINK.get(pp);
                                // END NOT IN KNUTH

                            }
                            // System.out.printf("AFTER  is %s\n", timpToString(u0^1));
                            // System.out.printf("BEFORE is %s\n", timpToString(v^1));
                            // Then set...
                            s = TSIZE[v ^ 1] - 1;
                            TSIZE[v ^ 1] = s;
                            t = TIMP.get(v ^ 1);
                            for (int i = 0; i < s; ++i) t = NEXT.get(t);  // XXX i = 1 or 0?
                            // System.out.printf("pair s=%d of TIMP(%d) is %d:%d @%d\n", s, dl(v^1), dl(U.get(t)), dl(V.get(t)), t);
                            // System.out.printf("The second t-cycle is %d-%d-%d-%d\n", t, LINK.get(t), LINK.get(LINK.get(t)), LINK.get(LINK.get(LINK.get(t))));

                            if (ppp != t) {  // swap pairs by setting
//                                System.out.printf("swapping pairs B %d:%d @%d <-> %d:%d @%d\n", dl(U.get(t)),
//                                        dl(V.get(t)), t,
//                                        dl(U.get(ppp)),
//                                        dl(V.get(ppp)),
//                                        ppp);
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
                            // System.out.printf(" AFTER is %s\n", timpToString(v^1));
                            // print();
                        }
                        // System.out.printf("*** post treatment of %d\n", dl(l0));
                        // print();
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
                    log.trace("state 10 E=%d F=%d BRANCH[%d]=%d",E,F,d,BRANCH[d]);
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
                        log.trace("d=%d. Retracting %d", d, dl(R[E]));
                        VAL[R[E] >> 1] = 0;
                    }
                case 12:  // Unfix real truths.
                    while (E > F) {
                        --E;
                        int X = R[E]>>1;
                        // reactivate the TIMP pairs that involve X and restore X to the free list (ex. 137)
                        for (int l0 = 2*X+1; l0 >= 2*X; --l0) {
                            // We have to work in the reverse order than we worked in step 7.
                            // We really hope not to have to do any memory allocation in the
                            // SAT solving loop. For the present we'll endure it while we get
                            // this working. Real solutions might involve having a PREV array
                            // to allow traversal in the opposite order of NEXT.

                            log.trace("Reactivating %d\n",dl(l0));
                            Stack<Integer> stack = new Stack<>();


                            for (int p = TIMP.get(l0), tcount = 0; tcount < TSIZE[l0]; p = NEXT.get(p), ++tcount) {
                                stack.push(p);
                            }
                            stack.forEach(p -> {
                                int u0 = U.get(p);
                                int v = V.get(p);
                                ++TSIZE[v^1];
                                ++TSIZE[u0^1];

                                // It is not entirely clear why this has to be done in a certain
                                // order (perhaps increasing TSIZE may reveal new entries in the
                                // TLIST, highlighting the fact that we need to check that in the
                                // iterations over TIMP.
                            });
                        }
                        VAL[X] = 0;
                    }
                case 13:  // Downdate BIMPs
                    if (BRANCH[d] >= 0) {
                        while (ISTACK.size() > BACKI[d]) {
                            Pair<Integer, Integer> top = ISTACK.pop();
                            BSIZE[top.getKey()] = top.getValue();
                        }
                    }
                case 14:  // Try again?
                    if (BRANCH[d] == 0) {
                        l = DEC[d];
                        DEC[d] = l = (l ^ 1);
                        BRANCH[d] = 1;
                        log.trace("d=%d. That didn't work, trying %d", d, dl(l));
                        state = 4;
                        continue;
                    }
                case 15:  // Backtrack.
                    log.trace("Backtracking from level %d", d);
                    if (d == 0) {
                        log.trace("UNSAT");
                        return Optional.empty();
                    }
                    --d;
                    E = F;
                    F = BACKF[d];
                    state = 12;
                    continue;
            }
        }
    }
}
