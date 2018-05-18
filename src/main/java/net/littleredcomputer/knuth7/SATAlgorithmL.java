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
    private static final int PT = NT - 2;

    static class Variable {
        int SIG = 0;  // binary signature discussed in the solution to F6 Exercise 149
        int SIGL = Integer.MAX_VALUE;  // "infinitely long:" cannot be a prefix of any actual branch history
        // TODO: hook up variable names with a method here when the SAT problem was supplied in knuth format.
    }

    static class Literal {
        Literal(int id) { this.id = id; }

        final int id;  // whatever you want (typically, the unencoded literal value)
        int TSIZE = 0;  // length of active segment of TIMP list
        int BSIZE = 0;  // length of active segment of BIMP list
        long IST = 0;
        int TIMP;  // index of first pair of implicants in U,V arrays
        final TIntArrayList BIMP = new TIntArrayList();

        // auxiliary data for Tarjan's algorithm
        long bstamp;  // bstamp value identifies current generation of candidates
        int rank;
        Literal parent;  // points to the parent of this vertex (which is another vertex or Λ.
        Literal vcomp;  // for component representatives: the component member of maximum rating
        int untagged;  // index of first arc originating at this vertex which remains untagged
        Literal link;  // link to next vertex in {active, settled} vertex stack
        Literal min;  // active vertex of smallest rank having the following property:
        // "Either u ≡ v or there is a directed path from v to u consisting of zero or
        //  more mature tree arcs followed by a single non-tree arc."

        // Knuth economizes on literal memory by reusing the untagged field for height,
        // and the min field for child.

        // XXX should we split them out as a courtesy to those who may read this code
        // in the future?

        Literal child;
        int height;

        final TIntArrayList arcs = new TIntArrayList();  // projection of BIMP table down to the set of candidate variables

        @Override
        public String toString() {
            StringBuffer sb = new StringBuffer();
            if (negated(id)) sb.append('~');
            // TODO: have var link; delegate to its toString method
            sb.append(thevar(id));
            return sb.toString();
        }
    }

    // An array of elements of this type represents the arrays LL and LO in [F6].
    // i.e.: LL[k] = looks[k].literal; LO[k] = looks[k].offset

    static class Lookahead {
        Literal literal = null;
        int offset = 0;
    }

    // These next 4 arrays all grow in sync.
    private final TIntArrayList U = new TIntArrayList();
    private final TIntArrayList V = new TIntArrayList();
    private final TIntArrayList LINK = new TIntArrayList();
    private final TIntArrayList NEXT = new TIntArrayList();
    private final TIntArrayList FORCE = new TIntArrayList();
    private final Literal[] lit;
    private final Variable[] var;
    private final Lookahead[] look;
    private final int[] VAR;
    private final int[] INX;  // INX[v] is the index of variable v in VAR
    private final int[] VAL;  // VAL[i] is the current contextual truth value of VAR[i]
    private final int[] DEC;
    private final int[] BACKF;  // backtrack value of F, indexed by depth
    private final int[] BACKI;  // backtrack value of ISTACK size, indexed by depth
    private final int[] BRANCH;
    private final int[] R;  // stack of literals
    // Reading Knuth we might choose to implement ISTACK as a stack of pairs of ints. But that would require boxing.
    // Instead, we implement ISTACK as a pair of stacks of primitive ints.
    private final TIntStack ISTACKb = new TIntArrayStack();  // stack of literals
    private final TIntStack ISTACKs = new TIntArrayStack();  // stack of BIMP table sizes for corresponding literals above
    private int T = NT;  // truth degree (F6 7.2.2.2 p. 37)
    private int E = 0;  // literals R[k] are "nearly true" for G <= k < E.
    private int F = 0;
    private int G = 0;
    private long ISTAMP = 0;  // Knuth points out (sat11.w:1528) that this could conceivably overflow a 32-bit int
    private long BSTAMP = 0;  // stamp value of current candidate list in algorithm X
    private int d = 0;  // current depth within search tree
    private int state = 2;  // currently executing step of algorithm L
    private int CONFLICT = 0;  // XXX we probably don't want this as an actual state variable.
    // We suspect it's only being used to allow a subroutine to influence the control flow of
    // its caller and there are other ways to do that.
    private int l = 0;  // Current branch literal
    private int SIG = 0;  // Current prefix of binary encoding of branch state
    private int SIGL = 0;
    boolean useX = false;  // whether to use algorithm X for lookahead
    int stopAtStep = -1;  // for testing purposes: abandon search at this step number
    boolean knuthCompatible = true;
    private enum Trace {STEP, SEARCH, LOOKAHEAD, BIMP, SCORE, FIXING, FOREST}
    EnumSet<Trace> tracing = /* EnumSet.noneOf(Trace.class) */ EnumSet.of(Trace.SEARCH);
    AlgorithmX x = null;

    private enum Fixity {
        UNFIXED,
        FIXED_T,
        FIXED_F
    }

    SATAlgorithmL(SATProblem p) {
        super("L", p);
        final int nVariables = problem.nVariables();
        final int literalAllocation = 2 * nVariables + 2;
        lit = new Literal[literalAllocation];
        Arrays.setAll(lit, Literal::new);
        var = new Variable[nVariables+1];
        Arrays.setAll(var, i -> new Variable());
        look = new Lookahead[literalAllocation];
        Arrays.setAll(look, i -> new Lookahead());
        VAR = new int[nVariables];
        VAL = new int[nVariables+1];
        DEC = new int[nVariables];
        BACKF = new int[nVariables];
        BACKI = new int[nVariables];
        INX = new int[nVariables + 1];
        BRANCH = new int[nVariables];
        R = new int[nVariables+1];  // stack to record the names of literals that have received values.
        // A literal and its complement never appear together here, so nVariables is enough space (but: one-based)

        Set<Integer> units = new HashSet<>();
        List<Set<Integer>> oBIMP = new ArrayList<>(literalAllocation);
        for (int i = 0; i < 2 * nVariables + 2; ++i) oBIMP.add(new HashSet<>());
        for (int i = 0; i < problem.nClauses(); ++i) {
            List<Integer> clause = problem.getEncodedClause(i);
            switch (clause.size()) {
                case 1: {
                    // Put it in the FORCE array, unless it is contradictory
                    final int u = clause.get(0);
                    if (units.contains(u ^ 1))
                        throw new IllegalArgumentException("Contradictory unit clauses involving variable " + thevar(u) + " found");
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
                    final int w = clause.get(0), v = clause.get(1), u = clause.get(2);

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

                    NEXT.add(lit[u ^ 1].TIMP);
                    NEXT.add(lit[v ^ 1].TIMP);
                    NEXT.add(lit[w ^ 1].TIMP);

                    lit[u ^ 1].TIMP = z;
                    lit[v ^ 1].TIMP = z + 1;
                    lit[w ^ 1].TIMP = z + 2;

                    ++lit[u ^ 1].TSIZE;
                    ++lit[v ^ 1].TSIZE;
                    ++lit[w ^ 1].TSIZE;

                    break;
                }
                default:
                    throw new IllegalArgumentException("Algorithm L can only cope with 3SAT at the moment " + clause.size());
            }
        }
        for (int l = 2; l < literalAllocation; ++l) {
            lit[l].BIMP.addAll(oBIMP.get(l));
            lit[l].BSIZE = lit[l].BIMP.size();
        }
        FORCE.addAll(units);

        // Knuth scrambles the order of the free variables here. I don't love this, since the
        // RNG he uses is also used for other randomization purposes: this makes the exact behavior
        // of the algorithm overly determined by details of the implementation, IMO.

        // Case in point: for the hash_bits array, which we are not using (yet),
        // Knuth generates 92*8 random numbers; to
        // get consistent results, we have to "burn" this many
        int seed = 0;
        SGBRandom rng = new SGBRandom(seed);
        for (int k = 92; k != 0; --k) for (int j = 0; j < 8; ++j) rng.nextRand();

        for (int k = 0; k < nVariables; ++k) {
            final int j = rng.unifRand(k+1);
            if (j != k) {
                int i = VAR[j];
                VAR[k] = i;
                INX[i] = k;
                VAR[j] = k+1;
                INX[k+1] = j;
            } else {
                VAR[k] = k + 1;
                INX[k + 1] = k;
            }
        }
    }

    /**
     * Propagate the literal l through all of the binary clauses using the BIMP table.
     * If a conflict is at any point, the propagation is abandoned early and false is
     * returned.
     */
    private boolean propagate(int l) {
        int H = E;
        if (!takeAccountOf(l, false)) {
            return false;
        }
        for (; H < E; ++H) {
            TIntArrayList bimpl = lit[R[H]].BIMP;
            for (int i = 0; i < lit[R[H]].BSIZE; ++i) {
                final int l1 = bimpl.getQuick(i);
                if (!takeAccountOf(l1, true)) return false;
            }
        }
        return true;
    }

    /**
     * Implements equation (62) of 7.2.2.2. Returns false if the next step is CONFLICT.
     */
    private boolean takeAccountOf(int l, boolean subordinate) {
        switch (fixity(l)) {
            case FIXED_T: {
                break;
            }
            case FIXED_F: {
                return /* conflict */ false;
            }
            case UNFIXED:
                if (tracing.contains(Trace.FIXING)) log.trace("%s%sfixing %d", subordinate ? " " : "", tName(T), dl(l));
                VAL[thevar(l)] = T + (l & 1);
                R[E] = l;
                ++E;
        }
        return true;
    }

    /* True if BIMP[b] contains l. */
    private boolean bimpContains(int b, int l) {
        TIntArrayList bimpl = lit[b].BIMP;
        for (int i = 0; i < lit[b].BSIZE; ++i) if (bimpl.get(i) == l) return true;
        return false;
    }

    /* Append l to BIMP[b], allowing for an undo in the future. */
    private void appendToBimp(int b, int l) {
        final int bsize = lit[b].BSIZE;
        if (lit[b].IST != ISTAMP) {
            lit[b].IST = ISTAMP;
            ISTACKb.push(b);
            ISTACKs.push(bsize);
        }
        TIntArrayList bimp = lit[b].BIMP;
        if (bimp.size() > bsize) bimp.set(bsize, l);
        else if (bimp.size() == bsize) bimp.add(l);
        else throw new IllegalStateException("bimp size invariant violation");
        ++lit[b].BSIZE;
    }

    private static int dl(int literal) {
        // TODO: hook this up to variable names if source problem was given in Knuth format
        return SATProblem.decodeLiteral(literal);
    }

    private void maintainPrefix(int l) {
        Variable v = var[thevar(l)];
        int q = v.SIGL;
        if (q < SIGL) {
            int t = SIG;
            // Knuth writes 1LL below, but it's not obvious why
            if (q < 32) t &= -(1<<(32-q));
            if (v.SIG != t) {
                v.SIG = SIG;
                v.SIGL = SIGL;
            }
        } else {
            v.SIG = SIG;
            v.SIGL = SIGL;
        }
    }

    /**
     * Implements steps L8 and L9 of Algorithm L. Returns false if the next step is CONFLICT.
     */
    private boolean consider(int u, int v) {
        // if (log.isTraceEnabled()) log.trace("consider %d∨%d", dl(u), dl(v));
        // STEP L8: Consider u ∨ v
        Fixity fu = fixity(u);
        Fixity fv = fixity(v);

        if (fu == Fixity.FIXED_T || fv == Fixity.FIXED_T) return true;
        else if (fu == Fixity.FIXED_F && fv == Fixity.FIXED_F) return false;
        else if (fu == Fixity.FIXED_F && fv == Fixity.UNFIXED) return propagate(v);
        else if (fv == Fixity.FIXED_F && fu == Fixity.UNFIXED) return propagate(u);
        // Variable prefix maintenance (See F6 Ex. 149)
        maintainPrefix(u);
        maintainPrefix(v);
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
        int val = VAL[thevar(l)];
        if (val < T) return Fixity.UNFIXED;
        return (val & 1) == (l & 1) ? Fixity.FIXED_T : Fixity.FIXED_F;
    }


    private String timpToString(int l) {
        StringBuilder sb = new StringBuilder();
        sb.append(String.format("  %3d: ", dl(l)));
        for (int i = 0, p = lit[l].TIMP; i < lit[l].TSIZE; i++, p = NEXT.get(p)) {
            sb.append(dl(U.get(p))).append(':').append(dl(V.get(p))).append(' ');
        }
        return sb.toString();
    }

    private void print() {
        final int nVariables = problem.nVariables();
        log.trace("BIMP tables:");
        for (int l = 2; l <= 2*nVariables+1; ++l) {
            final int bsize = lit[l].BSIZE;
            if (bsize < 0) throw new IllegalStateException(String.format("bad BIMP at %d (%d): %d", l, dl(l), bsize));
            if (bsize > 0) {
                TIntArrayList b = lit[l].BIMP;
                StringBuilder sb = new StringBuilder();
                sb.append(String.format("  %3d: ", dl(l)));
                for (int i = 0; i < bsize; ++i) sb.append(dl(b.get(i))).append(' ');
                log.trace(sb.toString());
            }
        }
        log.trace("TIMP tables:");
        for (int l = 2; l <= 2*nVariables+1; ++l) {
            if (lit[l].TSIZE > 0) {
                log.trace(timpToString(l));
            }
        }
        log.trace("E=%d F=%d G=%d VAR %s VAL %s", E, F, G, Arrays.toString(VAR), Arrays.toString(VAL));
    }

    private String stateToString() {
        return nodeCount + "n " + Arrays.stream(VAL).skip(1).mapToObj(i -> i == 0 ? "\u00b7" : (i&1) == 0 ? "1" : "0").collect(Collectors.joining());
    }

    @Override
    public Optional<boolean[]> solve() {
        if (useX && x == null) {
            x = new AlgorithmX();
        }
        start();
        final int N = VAR.length;

        // TODO: implement the idea of "compensation resolvents"

        STEP:
        while (true) {
            if (stepCount == stopAtStep) {
                log.error("Exhausted budget of solution steps at #%d. Returning UNSAT, " +
                        "but this is not certain as the search was abandoned.", stepCount);
                return Optional.empty();
            }
            ++stepCount;
            if (stepCount % logCheckSteps == 0) {
                maybeReportProgress(this::stateToString);
            }
            if (tracing.contains(Trace.STEP)) log.trace(">>>> step %d state %d", stepCount, state);
            switch (state) {
                case 2:  // New node.
                    ++nodeCount;
                    if (tracing.contains(Trace.BIMP)) print();
                    if (FORCE.isEmpty() && F < N && useX) {
                        boolean ok = x.X();
                        if (!ok) {
                            // Go to state 15 if alg. X has discovered a conflict.
                            if (tracing.contains(Trace.STEP)) log.trace("Alg. X detected a contradiction");
                            state = 15;
                            continue;
                        } else {
                            if (tracing.contains(Trace.STEP)) log.trace("Alg. X has returned");
                        }
                    }
                    // Step X1:  Satisfied?
                    if (F == N) {
                        boolean sat[] = new boolean[N];
                        for (int i = 1; i <= N; ++i) sat[i-1] = (VAL[i] & 1) == 0;
                        return Optional.of(sat);
                    }
                    if (FORCE.size() > 0) {
                        state = 5;
                        continue;
                    }
                    BRANCH[d] = -1;
                    SIGL = d;
                case 3: {  // Choose l.
                    if (useX) {
                        // Exercise 168 says:
                        // Find the l in Lookahead.literal with l mod 2 == 0 and and
                        // max (H(l)+.1)(H(l+1)+.1). If l is fixed, set l = 0 (in that
                        // case, algorithm X found at least one forced literal, although
                        // U (i.e., FORCE.size()) is now zero; we want to do another
                        // lookahead before branching again. Otherwise if H(l) > H(l+1)
                        // then ++l.
                        double maxz = 0;
                        for (int i = 0; i < x.S; ++i) {
                            int cl = look[i].literal.id;
                            if (negated(cl)) continue;
                            double z = (x.H[cl] + 0.1) * (x.H[cl+1] + 0.1);
                            if (tracing.contains(Trace.SCORE)) log.trace(" %d, %.4f:%.4f (%.4f)", dl(cl), x.H[cl], x.H[cl+1], z);
                            if (z > maxz) {
                                maxz = z;
                                l = cl;
                            }
                        }
                        Fixity f = fixity(l);
                        if (VAL[thevar(l)] >= RT) l = 0;
                        else if (x.H[l] > x.H[l+1]) ++l;
                        if (tracing.contains(Trace.SEARCH)) log.trace("The heuristic data indicated the choice of %d", dl(l));
                    } else l = 2*VAR[0]+1; // trivial heuristic: deny the first free variable
                    if (l == 0) {
                        log.trace("no branch at level %d", d);
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
                    if (tracing.contains(Trace.STEP)) { log.trace("d=%d: Trying %d", d, dl(l)); }
                    SIGL = d+1;
                    FORCE.resetQuick();
                    FORCE.add(l);
                case 5:  // Accept near truths.
                    if (tracing.contains(Trace.SEARCH)) log.trace("Accepting near-truths");
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

                case 6: { // Choose a nearly true l.
                    if (G == E) {
                        state = 10;
                        continue;
                    }
                    int L = R[G];
                    ++G;
                    // case 7:  Promote L to real truth.
                    int X = thevar(L);
                    VAL[X] = RT + (L & 1);
                    // Remove variable X from the free list and from all TIMP pairs (ex. 137).
                    final int N1 = N - G;
                    int x = VAR[N1];
                    int j = INX[X];
                    VAR[j] = x;
                    INX[x] = j;
                    VAR[N1] = X;
                    INX[X] = N1;
                    for (int xlit = 2 * X; xlit <= 2 * X + 1; ++xlit) {
                        for (int p = lit[xlit].TIMP, tcount = 0; tcount < lit[xlit].TSIZE; p = NEXT.get(p), ++tcount) {
                            int u0 = U.get(p);
                            int v = V.get(p);
                            int pp = LINK.get(p);
                            int ppp = LINK.get(pp);
                            int s = lit[u0^1].TSIZE - 1;
                            lit[u0 ^ 1].TSIZE = s;
                            int t = lit[u0 ^ 1].TIMP;
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
                                V.set(t, xlit ^ 1);
                                LINK.set(t, ppp);

                                // NOT IN KNUTH: reset pp.
                                pp = t;
                                // END NOT IN KNUTH
                            }
                            // Then set...
                            s = lit[v ^ 1].TSIZE - 1;
                            lit[v ^ 1].TSIZE = s;
                            t = lit[v ^ 1].TIMP;
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
                                U.set(t, xlit ^ 1);
                                V.set(t, u0);
                                LINK.set(t, p);
                            }
                        }
                    }

                    // Do step L8 for all pairs (u,v) in TIMP(L) then return to L6.
                    for (int p = lit[L].TIMP, tcount = 0; tcount < lit[L].TSIZE; p = NEXT.get(p), ++tcount) {
                        final int u = U.get(p), v = V.get(p);
                        if (tracing.contains(Trace.FIXING)) log.trace("  %d->%d|%d", dl(L), dl(u), dl(v));
                        boolean conflict = !consider(u, v);
                        if (conflict) {
                            state = this.CONFLICT;
                            continue STEP;
                        }
                    }
                    state = 6;
                    continue;
                }
                /* Steps 8 and 9 are in the method consider(). */
                case 10:  // Accept real truths.
                    if (tracing.contains(Trace.FIXING)) log.trace("state 10 E=%d F=%d BRANCH[%d]=%d",E,F,d,BRANCH[d]);
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
                        // if (log.isTraceEnabled()) log.trace("Retracting %d", dl(R[E]));
                        VAL[thevar(R[E])] = 0;
                    }
                case 12:  // Unfix real truths.
                    while (E > F) {
                        --E;
                        int X = thevar(R[E]);
                        // reactivate the TIMP pairs that involve X and restore X to the free list (ex. 137)
                        for (int xlit = 2*X + 1; xlit >= 2*X; --xlit) {
                            if (tracing.contains(Trace.BIMP)) log.trace("Reactivating %d",dl(xlit));
                            // Knuth insists (in the printed fascicle) that the downdating of TIMP should
                            // happen in the reverse order of the updating, which would seem to argue for
                            // traversing this linked list in reverse order. However, since each entry in
                            // the TIMP list will point (via U and V) to two strictly other TIMP lists, it's
                            // not clear why the order matters.
                            for (int p = lit[xlit].TIMP, tcount = 0; tcount < lit[xlit].TSIZE; p = NEXT.get(p), ++tcount) {
                                int u0 = U.get(p);
                                int v = V.get(p);
                                ++lit[v ^ 1].TSIZE;
                                ++lit[u0 ^ 1].TSIZE;
                            }
                        }
                        VAL[X] = 0;
                    }
                case 13:  // Downdate BIMPs
                    if (BRANCH[d] >= 0) {
                        while (ISTACKb.size() > BACKI[d]) {
                            lit[ISTACKb.pop()].BSIZE = ISTACKs.pop();
                        }
                    }
                case 14:  // Try again?
                    if (BRANCH[d] == 0) {
                        // Move to branch 1.  Add a 1 bit to the binary prefix string, unless it is already long enough.
                        // We don't add zero bits at branch zero. Instead, the prefix starts out at zero, and 1-bits are
                        // retracted at backtrack time, so we don't need to push 0-bits into the prefix.
                        if (d < 32) SIG |= 1<<(31-d);
                        l = DEC[d];
                        DEC[d] = l = (l ^ 1);
                        BRANCH[d] = 1;
                        if (tracing.contains(Trace.SEARCH)) log.trace("d=%d. That didn't work, trying %d", d, dl(l));
                        state = 4;
                        continue;
                    }
                case 15:  // Backtrack.
                    if (tracing.contains(Trace.SEARCH)) log.trace("Backtracking from level %d", d);
                    if (d == 0) {
                        log.trace("UNSAT after %d nodes", nodeCount);
                        return Optional.empty();
                    }
                    --d;
                    if (d < 31) SIG &= -(1<<(31-d));  // Remove a bit from the binary prefix string
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
    class AlgorithmX {
        private final TIntArrayList CAND = new TIntArrayList();  // candidate variables for algorithm X
        private final int[] CANDL;  // candidate literals for algorithm X

        final double alpha = 3.5;
        final double THETA = 20.0;
        final int C0 = 30, C1 = 600;  // See Ex. 148
        final int nVariables;
        private int l0 = 0;  // Current lookahead literal (used in algorithm X)
        int S;  // number of candidate literals
        double w = 0.0;  // Current weight of lookahead choice. TODO it is dodgy that this is an instance variable...
        final double[][] h;  // h[d][l] is the h-score ("rough heuristic") of literal l at depth d
        private final double[] H;  // H[l] is the "more discriminating" score for literal l at the current depth (Eq. 67)
        private final double[] r;  // r[x] is the "rating" of variable x in step X3 (one-based)

        AlgorithmX() {
            nVariables = problem.nVariables();
            h = new double[nVariables+1][];
            H = new double[2 * nVariables + 2];
            r = new double[nVariables + 1];
            CANDL = new int[2*nVariables];
        }

        double[] computeHeuristics() {
            final int N = nVariables - F;
            double[] hd = h[d];

            if (hd == null) {
                h[d] = hd = new double[2*nVariables+2];
                if (d <= 1) Arrays.fill(hd, 1);
                else System.arraycopy(h[d-1], 0, hd, 0, hd.length);
            }

            int nCycles = d <= 1 ? 5 : 1;

            // Step X1 is performed before this routine is called.
            // Step X2: Compile rough heuristics.
            for (int k = 0; k < nCycles; ++k) {
                double hAve = 0.0;
                for (int i = 0; i < N; ++i) {
                    final int vi = VAR[i];
                    hAve += hd[poslit(vi)] + hd[neglit(vi)];
                }
                hAve /= 2.0 * N;
                final double hAve2 = hAve * hAve;
                // TODO: this allocation needs to be killed; use Knuth's technique of alternating between two static arrays.
                double[] hprime = new double[hd.length];
                for (int i = 0; i < N; ++i) {
                    final int vi = VAR[i];
                    for (int l = 2*vi; l <= 2*vi+1; ++l) {
                        // update hd[l]
                        double hp = 0.1;
                        // for all u in BIMP[l] with u not fixed
                        TIntArrayList bimpl = lit[l].BIMP;
                        double hs = 0;
                        for (int j = 0; j < lit[l].BSIZE; ++j) hs += hd[bimpl.get(j)] / hAve;
                        hp += alpha * hs;
                        for (int p = lit[l].TIMP, j = 0; j < lit[l].TSIZE; p = NEXT.get(p), ++j) {
                            hp += hd[U.get(p)] * hd[V.get(p)] / hAve2;
                        }
                        hprime[l] = hp > THETA ? THETA : hp;
                    }
                }
                System.arraycopy(hprime, 2, hd, 2, 2*nVariables);
            }
            return hd;
        }

        /*
         * Put free variables into the CAND array. If participantsOnly, be sure to only admit variables which
         * are participants.
         */
        private void selectCandidates(boolean participantsOnly) {
            CAND.resetQuick();
            for (int i = 0; i < nVariables - F; ++i) {
                final int vi = VAR[i];
                // TODO: consider making val a property of the variable array

                VAL[vi] = 0;  // erase all former assignments
                if (participantsOnly) {
                    // Perform the prefix test. Skip to next free variable if it fails.
                    // Knuth sat11: if (x > primary_vars) continue;
                    Variable v = var[vi];
                    final int t = v.SIG, l = v.SIGL;
                    if (l == SIGL) {
                        if (t != SIG) continue;  // not a candidate. simple comparison since lengths are the same.
                    } else if (l > SIGL) continue;  // v's signature is too long to be a prefix of the current signature
                    else if (t != (l<32 ? SIG & -(1<<(32-l)) : SIG)) continue;  // prefixes don't match
                }
                if (tracing.contains(Trace.FOREST)) log.trace("adjoining candidate %d", vi);
                CAND.add(vi);
            }
        }

        /**
         * Knuth's Algorithm X, which is used to gather information guiding the selection of literals
         * in Algorithm L.
         */
        boolean X() {
            if (F == nVariables) {
                log.trace("Returning because F == N before we even start X");
                return true;
            }
            final int N = nVariables - F;
            final double[] hd = computeHeuristics();
            // Step X3: Preselect candidates.
            // First select all free participants.

            selectCandidates(SIGL > 0);

            if (CAND.size() == 0) {
                // "Terminate happily, however, if all free clauses are satisfied...."
                // From Ex. 152:
                //  "Indeed, the absence of free participants means that the fixed-true
                //   literals form an autarky. If TSIZE(l) is nonzero for any free literal
                //   l, some clause is unsatisfied. Otherwise all clauses are satisfied
                //   unless some free l has an unfixed literal lʹ ∈ BIMP(l)."
                boolean sat = true;
                VARIABLE: for (int vi = 0; vi < nVariables - F; ++vi) {
                    final int v = VAR[vi];
                    for (int l = 2*v; l <= 2*v+1; ++l) {
                        // l is a free literal since v is a free variable.
                        if (lit[l].TSIZE > 0) {
                            sat = false;
                            break VARIABLE;
                        }
                        TIntArrayList bimpl = lit[l].BIMP;
                        for (int j = 0; j < lit[l].BSIZE; ++j) {
                            if (fixity(bimpl.get(j)) == Fixity.UNFIXED) {
                                sat = false;
                                break VARIABLE;
                            }
                        }
                    }
                }
                if (sat) throw new IllegalStateException("X found SAT!");
                // Otherwise, if we didn't get lucky, add candidates non-selectively.
                selectCandidates(false);
            }

            // Give each variable x in CAND the rating r(x) = h(x)h(¬x)
            double r_sum = 0.;
            for (int i = 0; i < CAND.size(); ++i) {
                final int v = CAND.get(i);
                r[v] = hd[2*v] * hd[2*v+1];
                if (tracing.contains(Trace.SCORE)) log.trace("Rating(%d) = %g", v, r[v]);
                r_sum += r[v];
            }


            final double C_max = d == 0 ? C1 : Integer.max(C0, C1/d);  // Eq. (66)

            if (tracing.contains(Trace.SCORE)) log.trace("C_max = %g", C_max);

            // While C > 2 C_max, delete all elements of CAND whose rating
            // is less than the mean rating; but terminate the loop if no elements are
            // actually deleted.

            while (CAND.size() > 2 * C_max) {
                // Compute the mean score.
                final int sz = CAND.size();
                double r_mean = r_sum / sz;
                boolean deletions = false;
                r_sum = 0.0;
                for (int i = 0; i < sz; ) {
                    if (r[CAND.get(i)] < r_mean) {
                        // This is a bad one. Pull a new one from the end of the candidates list.
                        CAND.set(i, CAND.removeAt(sz-1));
                        deletions = true;
                    } else {
                        // This is a good one. Keep it, accumulate its score, and go to the next.
                        r_sum += r[CAND.get(i)];
                        ++i;
                    }
                }
                if (!deletions) break;
            }
            // Finally, if C > C_max, reduce C to C_max by retaining only top-ranked
            // candidates.
            if (CAND.size() > C_max) {
                // Here's an allocation. Maybe we want to put heapification under
                // user control. Can we also close over r[] that way... XXX
                IntHeap h = new IntHeap(CAND, (v,w) -> Double.compare(r[w], r[v]));
                while (CAND.size() > C_max) h.pop();
            }
            ++BSTAMP;
            // Mark surviving candidates with the new BSTAMP value, and compute big H with equation (67).
            Arrays.fill(H, 0);
            for (int i = 0; i < CAND.size(); ++i) {
                final int c = CAND.get(i);
                for (int candlit = 2*c; candlit <= 2*c+1; ++candlit) {
                    final Literal l = lit[candlit];
                    l.bstamp = BSTAMP;
                    l.arcs.resetQuick();
                    for (int j = l.TIMP, k = 0; k < l.TSIZE; j = NEXT.getQuick(j), ++k) {
                        //System.out.printf("%d => %d and %d\n", dl(l), dl(U.getQuick(j)), dl(V.getQuick(j)));
                        H[candlit] += hd[U.getQuick(j)] * hd[V.getQuick(j)];
                    }
                }
            }
            S = 0;
            // Compute candidate BIMP list.
            for (int i = 0; i < CAND.size(); ++i) {
                final int c = CAND.get(i);
                for (int candlit = 2*c; candlit <= 2*c+1; ++candlit) {
                    CANDL[S++] = candlit;
                    final Literal u = lit[candlit];
                    u.vcomp = u;  // A field we will use after resolving into strong components
                    TIntArrayList bimp = u.BIMP;
                    for (int j = 0; j < u.BSIZE; ++j) {
                        int v = bimp.getQuick(j);
                        if (v > candlit && lit[v].bstamp == BSTAMP) {
                            // Knuth: we add v --> u to the candidate arcs when there's an implication u => v in the BIMP table.
                            // We also add the arc ¬v --> ¬u. By enforcing v > candlit, we ensure that both directions are added
                            // atomically (the BIMP table contains both arrows, but not contiguously; if we are going to cap
                            // the number of arcs we consider, it is important that we don't strand one arc of a pair outside
                            // the graph).
                            // log.trace("arc for %d: %d -> %d, %d -> %d", dl(candlit), dl(v), dl(candlit), dl(not(candlit)), dl(not(v)));
                            lit[v].arcs.add(candlit);
                            lit[candlit^1].arcs.add(v^1);
                        }
                    }
                }
            }

            // One Weird Trick: do we need to reverse the order of the arcs to get our components out in the right
            // order?

            if (knuthCompatible) {
                for (int i = 0; i < S; ++i) {
                    Literal l = lit[CANDL[i]];
                    l.arcs.reverse();
                }
            }

            // X4 [Nest the candidates.]

            ConnectedComponents cc = new ConnectedComponents(lit);
            cc.find(CANDL, S);


            // TODO: Knuth's Tarjan algorithm is modified to notice when ~v lives in v's SCC.
            // Our implementation does not notice this, but it would be easy to check, for
            // all literals among the candidates, that


            // Rip over the components, finding, within each, the literal of maximum rating
            // (this is used as an alternate component representative.) We also check here
            // to see if a component contains a literal contradictory to its CC representative.

            for (int i = 0; i < S; ++i) {
                final Literal l = lit[CANDL[i]];
                // TODO: consider equipping literals with a pointer to their variable parents
                if (l != l.parent && r[thevar(l.id)] > r[thevar(l.parent.vcomp.id)]) {
                    l.parent.vcomp = l;
                }
                // XXX this is "goto look_bad" in Knuth
                if (l.id == not(l.parent.id)) throw new IllegalStateException("contradiction discovered in lookahead");
            }

            if (tracing.contains(Trace.FOREST)) {
                log.trace("Strong components:");
                for (Literal s = cc.settled(); s != null; s = s.link) {
                    final Literal t = s;
                    log.trace(() -> {
                        StringBuilder sb = new StringBuilder(String.format(" %d %.4g", dl(t.id), r[thevar(t.id)]));
                        if (t.parent != t) sb.append(" with ").append(dl(t.parent.id));
                        else if (t.vcomp != t) sb.append("-> ").append(dl(t.vcomp.id)).append(String.format(" %.4g", r[t.vcomp.id >> 1]));
                        return sb.toString();
                    });
                }
            }


            // Find the heights and the child/sibling links
            final Literal root = lit[1];
            {
                root.child = null;
                root.height = -1;
                Literal uu, p, pp = root, w = null;
                int height = 0;
                for (Literal u = cc.settled(); u != null; u = uu) {
                    uu = u.link;
                    p = u.parent;
                    if (p != pp) {
                        height = 0;
                        w = root;
                        pp = p;
                    }
                    TIntArrayList arcs = lit[not(u.id)].arcs;
                    // log.trace("arcs = " + Arrays.stream(arcs.toArray()).mapToObj(a -> lit[a].toString()).collect(Collectors.joining(",")));
                    for (int j = 0; j < arcs.size(); ++j) {
                        Literal v = lit[not(arcs.getQuick(j))];
                        Literal vv = v.parent;
                        if (vv == p) continue;
                        final int hh = vv.height;
                        if (hh >= height) {
                            height = hh + 1;
                            w = vv;
                        }
                    }
                    if (p == u) {
                        Literal v = w.child;
                        u.height = height;
                        u.child = null;
                        u.link = v;
                        w.child = u;
                    }
                }
            }

            if (tracing.contains(Trace.FOREST)) {
                for (int i = 0; i < 2*CAND.size(); ++i) {
                    Literal l = lit[CANDL[i]];
                    log.trace("  %d: height %d, child %s, link %s", dl(l.id), l.height,
                            l.child != null ? dl(l.child.id) : 0,
                            l.link != null ? dl(l.link.id) : 0);
                }
            }

            // Construct a sequence of literals LL[j] and corresponding truth offsets LO[j], for 0 <= j < S.
            // This is the "lookahead forest."

            int looks = 0;
            {
                int j = 0;
                Literal u = root.child, v = null;
                LOOK: while (true) {
                    look[looks].literal = u.vcomp;
                    u.rank = looks++;  // k advances in preorder
                    if (u.child != null) {
                        u.parent = v;  // fix parent temporarily for traversal
                        v = u;
                        u = u.child;  // descend to u's descendants
                    } else {
                        boolean more = true;
                        while (more) {
                            more = false;
                            /* post: */
                            int i = u.rank; /* label post */
                            look[i].offset = j;
                            j += 2;  // j advances in postorder
                            if (v != null) u.parent = v.vcomp;  // fix parent for lookahead
                            else u.parent = null;
                            if (u.link != null) u = u.link;  // move to u's next sibling
                            else if (v != null) {
                                u = v;
                                v = u.parent;  // after the last sibling, move to u's parent
                                more = true;  //  in Knuth: goto post, where post is a label marked above
                            } else break LOOK;
                        }
                    }
                }
                if (j != looks + looks) throw new IllegalStateException("confusion(looks)");
            }

            if (tracing.contains(Trace.FOREST)) {
                log.trace("Looks at level %d", d);
                for (int i = 0; i < looks; ++i) {
                    log.trace(" %d %d", dl(look[i].literal.id), look[i].offset);
                }
            }

            // X5 [Prepare to explore.]

            int Up = 0, jp = 0, j = 0;
            int BASE = 2;  // Knuth sets BASE = 0 in F6, but sets BASE = 2 in sat11.w
            int xstate = 6;
            // Move to avoid allocation. When to reset this?

            STEP: while (true) {
                //System.out.printf("X in state %d. j = %d\n", xstate, j);
                switch (xstate) {
                    case 6: { // [Choose l for lookahead.]
                        l = look[j].literal.id;
                        T = BASE + look[j].offset;
                        H[l] = lit[l].parent != null ? H[lit[l].parent.id] : 0;
                        if (tracing.contains(Trace.LOOKAHEAD)) log.trace("state 6 considers: %d @%d H=%.4g j=%d f=%s", dl(l), T, H[l], j, fixity(l));

                        Fixity f = fixity(l);
                        if (f == Fixity.UNFIXED) {
                            xstate = 8;
                            continue;
                        }
                        if (f == Fixity.FIXED_F && VAL[thevar(l)] < PT) {
                            if (!X12(not(l))) {
                                xstate = 13;
                                continue;
                            }
                        }
                    }
                    /* fall through */
                    case 7:  // [Move to next.]
                        // System.out.printf("now state 7\n");
                        if (FORCE.size() > Up) {
                            Up = FORCE.size();
                            jp = j;
                        }
                        ++j;
                        if (j == S) {
                            j = 0;
                            BASE += 2 * S;
                        }
                        if (j == jp || j == 0 && BASE + 2 * S >= PT) return true;
                        xstate = 6; continue;
                    case 8: { // [Compute sharper heuristic.]
                        //System.out.printf("now state 8...\n");
                        if (!Perform72()) { xstate = 13; continue; }
                        // Then...
                        if (w > 0) {
                            if (tracing.contains(Trace.SCORE)) log.trace("After P72() we have w = %.4g", w);
                            H[l0] += w;
                            xstate = 10;
                            continue;
                        }
                    }
                    case 9:  // [Exploit an autarky.]
                        if (H[l0] == 0) {
                            if (tracing.contains(Trace.LOOKAHEAD)) log.trace("autarky (a) at %d\n", dl(l0));
                            if (!X12(l0)) {
                                xstate = 13;
                                continue;
                            }
                        } else {
                            // TODO: change l0 to a Literal, or at least cache the value of lit[l0]
                            if (tracing.contains(Trace.SEARCH)) log.trace("autarky (b) at %s", lit[l0]);
                            // Generate the binary clause l0 | ~PARENT(l0)
                            appendToBimp(not(l0), not(lit[l0].parent.id));
                            appendToBimp(lit[l0].parent.id, l0);
                        }
                    case 10:  // [Optionally look deeper.]
                    case 11:  // [Exploit necessary assignments.]
                        TIntArrayList bimp = lit[not(l0)].BIMP;
                        for (int i = 0; i < lit[not(l0)].BSIZE; ++i) {
                            int u = bimp.getQuick(i);
                            Fixity f = fixity(u);
                            if (f == Fixity.FIXED_T && VAL[thevar(u)] < PT) X12(u);
                        }
                        xstate = 7;
                        continue;
                    case 13:  // [Recover from conflict.]
                        if (tracing.contains(Trace.LOOKAHEAD)) log.trace("lookahead conflict at %s", lit[l0]);
                        if (T < PT) {
                            l = not(l0);
                            if (!X12(l)) {
                                return false;
                            }
                            xstate = 7;
                            continue ;
                        }
                        return false;  // we have discovered a contradiction
                    default:
                        throw new IllegalStateException();
                }
            }
        }

        boolean Perform72() {
            l0 = l;
            w = 0;
            G = E = F;
            // allocation
            TIntArrayList W = new TIntArrayList();
            // log.trace("%sfixing %d", tName(T), dl(l));
            if (!propagate(l)) return false;  // Perform (62).
            while (G < E) {
                Literal L = lit[R[G]];
                ++G;
                // take account of (u, v) for all (u, v) in TIMP(L)
                for (int t = 0, p = L.TIMP; t < L.TSIZE; ++t, p = NEXT.getQuick(p)) {
                    int u = U.getQuick(p), v = V.getQuick(p);
                    if (tracing.contains(Trace.FIXING)) log.trace("  looking %d->%d|%d", dl(L.id), dl(u), dl(v));
                    Fixity fu = fixity(u), fv = fixity(v);
                    if (fu == Fixity.FIXED_T || fv == Fixity.FIXED_T) continue;
                    if (fu == Fixity.FIXED_F && fv == Fixity.FIXED_F) {
                        if (tracing.contains(Trace.FIXING)) log.trace("P72 contradiction: both fixed false");
                        return false;
                    }
                    if (fu == Fixity.FIXED_F && fv == Fixity.UNFIXED) {
                        if (!propagate(v)) {
                            if (tracing.contains(Trace.FIXING)) log.trace("P72 contradiction: failed to propagate %s", lit[v]);
                            return false;
                        }
                        W.add(v);
                    }
                    else if (fu == Fixity.UNFIXED && fv == Fixity.FIXED_F) {
                        if (!propagate(u)) {
                            if (tracing.contains(Trace.FIXING)) log.trace("P72 contradiction: failed to propagate %s", lit[u]);
                            return false;
                        }
                        W.add(u);
                    }
                    else {
                        assert fu == Fixity.UNFIXED && fv == Fixity.UNFIXED;
                        w += h[d][u] * h[d][v];
                    }
                }
                // generate new binary clauses (lbar_0 | w) for w in W.
                for (int i = 0; i < W.size(); ++i) {
                    int wi = W.getQuick(i);
                    appendToBimp(l0, wi);
                    appendToBimp(not(wi), not(l0));
                }
            }
            return true;
        }

        boolean X12(int l) {
            if (tracing.contains(Trace.FIXING)) log.trace("forcing %d", dl(l));
            FORCE.add(l);
            int oldT = T;
            T = PT;
            boolean result = Perform72();
            T = oldT;
            return result;
        }
    }

    private String tName(int t) {
        if (t >= RT) return "real";
        if (t >= NT) return "near";
        if (t >= PT) return "proto";
        return Integer.toString(t);
    }


}
