package net.littleredcomputer.knuth7;

import com.google.common.collect.Lists;
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

    static class Variable implements Comparable<Variable> {
        Variable(int id) { this.id = id; }
        final int id;  // one-based variable index
        int SIG = 0;  // binary signature discussed in the solution to F6 Exercise 149
        int SIGL = Integer.MAX_VALUE;  // "infinitely long:" cannot be a prefix of any actual branch history
        int VAL;  // current assigned value. The values are drawn from a belief hierarchy and may be "fixed" at different levels.
        int INX;  // our position in the VAR array
        // TODO: hook up variable names with a method here when the SAT problem was supplied in knuth format.
        float rating;

        // This ordering is used during the process of winnowing the lookahead candidate heap
        @Override public int compareTo(Variable o) { return Float.compare(rating, o.rating); }
    }

    static class Literal {
        Literal(int id) { this.id = id; }

        Variable var;  // pointer to our corresponding variable; this is |l| in Knuth notation
        final int id;  // whatever you want (typically, the unencoded literal value)
        Literal not;  // points to negation of this literal. In principle, this is final.
        int TSIZE = 0;  // length of active segment of TIMP list
        int BSIZE = 0;  // length of active segment of BIMP list
        long IST = 0;
        int TIMP;  // index of first pair of implicants in U,V arrays
        // final TIntArrayList BIMP = new TIntArrayList();
        List<Literal> BIMP;

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
        float H;  // the "refined" heuristic score

        final List<Literal> arcs = new ArrayList<>();

        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder();
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
    private final List<Literal> FORCE = new ArrayList<>();
    private final Literal[] lit;
    private final Variable[] var;
    private final Lookahead[] look;
    private final Variable[] VAR;
    private final Literal[] DEC;
    private final int[] BACKF;  // backtrack value of F, indexed by depth
    private final int[] BACKI;  // backtrack value of ISTACK size, indexed by depth
    private final int[] BRANCH;
    private final Literal[] R;  // stack of literals
    // Reading Knuth we might choose to implement ISTACK as a stack of pairs of ints. But that would require boxing.
    // Instead, we implement ISTACK as a pair of stacks of primitive ints.
    private final Stack<Literal> ISTACKb = new Stack<>();  // stack of literals
    private final TIntStack ISTACKs = new TIntArrayStack();  // stack of BIMP table sizes for corresponding literals above
    private int T = NT;  // truth degree (F6 7.2.2.2 p. 37)
    private int E = 0;  // literals R[k] are "nearly true" for G <= k < E.
    private int F = 0;
    private int G = 0;
    private long ISTAMP = 0;  // Knuth points out (sat11.w:1528) that this could conceivably overflow a 32-bit int
    private long BSTAMP = 0;  // stamp value of current candidate list in algorithm X
    private int d = 0;  // current depth within search tree
    private int state = 2;  // currently executing step of algorithm L
    // We suspect it's only being used to allow a subroutine to influence the control flow of
    // its caller and there are other ways to do that.
    private Literal l = null;  // Current branch literal
    private int SIG = 0;  // Current prefix of binary encoding of branch state
    private int SIGL = 0;
    boolean useX = true;  // whether to use algorithm X for lookahead
    int stopAtStep = -1;  // for testing purposes: abandon search at this step number
    boolean knuthCompatible = true;

    private enum Trace {STEP, SEARCH, LOOKAHEAD, BIMP, SCORE, FIXING, FOREST}

    EnumSet<Trace> tracing = /* EnumSet.noneOf(Trace.class) */ EnumSet.of(Trace.SEARCH, Trace.SCORE);
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
        var = new Variable[nVariables + 1];
        Arrays.setAll(var, Variable::new);
        lit = new Literal[literalAllocation];
        Arrays.setAll(lit, Literal::new);
        for (int i = 0; i < lit.length; ++i) {
            lit[i].not = lit[not(i)];
            lit[i].var = var[thevar(i)];
        }
        look = new Lookahead[literalAllocation];
        Arrays.setAll(look, i -> new Lookahead());
        VAR = new Variable[nVariables];
        DEC = new Literal[nVariables];
        BACKF = new int[nVariables];
        BACKI = new int[nVariables];
        BRANCH = new int[nVariables + 1];
        R = new Literal[nVariables + 1];  // stack to record the names of literals that have received values.
        // A literal and its complement never appear together here, so nVariables is enough space (but: one-based)

        Set<Integer> units = new HashSet<>();
        List<Set<Integer>> oBIMP = new ArrayList<>(literalAllocation);
        for (int i = 0; i < 2 * nVariables + 2; ++i) oBIMP.add(new HashSet<>());
        // We process the clauses in reverse order because Knuth does. This means our BIMP and TIMP tableaux
        // will be initialized with the same data in the same order as sat11.w.

        Lists.reverse(problem.encodedClauses()).forEach(clause -> {
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
                    // Put it in the BIMP. Choosing v, u in this order produces a Knuth-compatible BIMP table.
                    final int v = clause.get(0), u = clause.get(1);
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
        });
        for (int l = 2; l < literalAllocation; ++l) {
            lit[l].BIMP = oBIMP.get(l).stream().map(i -> lit[i]).collect(Collectors.toList());
            lit[l].BSIZE = lit[l].BIMP.size();
        }
        units.forEach(i -> FORCE.add(lit[i]));
        if (!FORCE.isEmpty() && tracing.contains(Trace.SEARCH)) log.trace("initially forcing %s", FORCE);
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
            final int j = rng.unifRand(k + 1);
            if (j != k) {
                Variable i = VAR[j];
                VAR[k] = i;
                i.INX = k;
                VAR[j] = var[k + 1];
                var[k + 1].INX = j;
            } else {
                VAR[k] = var[k + 1];
                var[k + 1].INX = k;
            }
        }
        print();
    }

    /**
     * Propagate the literal l through all of the binary clauses using the BIMP table.
     * If a conflict is at any point, the propagation is abandoned early and false is
     * returned.
     */
    private boolean propagate(Literal l) {
        int H = E;
        if (!takeAccountOf(l, false)) {
            return false;
        }
        for (; H < E; ++H) {
            List<Literal> bimpl = R[H].BIMP;
            // TODO: type of R
            for (int i = 0; i < R[H].BSIZE; ++i) {
                if (!takeAccountOf(bimpl.get(i), true)) return false;
            }
        }
        return true;
    }

    /**
     * Implements equation (62) of 7.2.2.2. Returns false if the next step is CONFLICT.
     */
    private boolean takeAccountOf(Literal l, boolean subordinate) {
        switch (fixity(l)) {
            case FIXED_T: {
                break;
            }
            case FIXED_F: {
                return /* conflict */ false;
            }
            case UNFIXED:
                if (tracing.contains(Trace.FIXING)) log.trace("%s%sfixing %d", subordinate ? " " : "", tName(T), l);
                // TODO: put VAL in the VAR array
                l.var.VAL = T + (l.id & 1);
                // TODO: type of R
                R[E] = l;
                ++E;
        }
        return true;
    }

    /* True if BIMP[b] contains l. */
    private boolean bimpContains(Literal b, Literal l) {
        final List<Literal> bimpl = b.BIMP;
        for (int i = 0; i < b.BSIZE; ++i) if (bimpl.get(i) == l) return true;
        return false;
    }

    /* Append l to BIMP[b], allowing for an undo in the future. */
    private void appendToBimp(Literal b, Literal l) {
        final int bsize = b.BSIZE;
        if (b.IST != ISTAMP) {
            b.IST = ISTAMP;
            // TODO: type of ISTACKb
            ISTACKb.push(b);
            ISTACKs.push(bsize);
        }
        List<Literal> bimp = b.BIMP;
        if (bimp.size() > bsize) bimp.set(bsize, l);
        else if (bimp.size() == bsize) bimp.add(l);
        else throw new IllegalStateException("bimp size invariant violation");
        ++b.BSIZE;
        assert bimpContains(b, l);  // TODO: get rid of this
    }

    private static int dl(int literal) {
        // TODO: hook this up to variable names if source problem was given in Knuth format
        return SATProblem.decodeLiteral(literal);
    }

    private void maintainPrefix(Literal l) {
        Variable v = l.var;
        int q = v.SIGL;
        if (q < SIGL) {
            int t = SIG;
            // Knuth writes 1LL below, but it's not obvious why
            if (q < 32) t &= -(1 << (32 - q));
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
    private boolean consider(Literal u, Literal v) {
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
        if (bimpContains(u.not, v.not)) return propagate(u);
        else if (bimpContains(u.not, v)) return true;
        else if (bimpContains(v.not, u.not)) return propagate(v);
        // Append v to BIMP(¬u), u to BIMP(¬v).
        appendToBimp(u.not, v);
        appendToBimp(v.not, u);
        return true;
    }

    /* Returns the fixity of l in the context T */
    private Fixity fixity(Literal l) {
        // TODO: want something like l.var.VAL
        int val = l.var.VAL;
        if (val < T) return Fixity.UNFIXED;
        return negated(val) == negated(l.id) ? Fixity.FIXED_T : Fixity.FIXED_F;
    }


    private String timpToString(int l) {  // TODO: type of l
        StringBuilder sb = new StringBuilder();
        sb.append(String.format("  %3d -> ", dl(l)));
        for (int i = 0, p = lit[l].TIMP; i < lit[l].TSIZE; i++, p = NEXT.get(p)) {
            sb.append(dl(U.get(p))).append('|').append(dl(V.get(p))).append(' ');
        }
        return sb.toString();
    }

    private void print() {
        final int nVariables = problem.nVariables();
        log.trace("BIMP tables:");
        for (int l = 2; l <= 2 * nVariables + 1; ++l) {
            final int bsize = lit[l].BSIZE;
            if (bsize < 0) throw new IllegalStateException(String.format("bad BIMP at %d (%d): %d", l, dl(l), bsize));
            if (bsize > 0) {
                // TODO: type of l
                log.trace("  %3s: %s", lit[l], lit[l].BIMP.stream().limit(bsize).map(Literal::toString).collect(Collectors.joining(" ")));
            }
        }
        log.trace("TIMP tables:");
        for (int l = 2; l <= 2 * nVariables + 1; ++l) {
            // TODO: type of l
            if (lit[l].TSIZE > 0) {
                log.trace(timpToString(l));
            }
        }
    }

    private String stateToString() {
        return nodeCount + "n " + Arrays.stream(var).skip(1).map(v -> v.VAL == 0 ? "\u00b7" : (v.VAL & 1) == 0 ? "1" : "0").collect(Collectors.joining());
    }

    @Override
    public Optional<boolean[]> solve() {
        if (useX && x == null) {
            x = new AlgorithmX();
        }
        start();
        final int N = VAR.length;

        // TODO: implement the idea of "compensation resolvents"

        TIntArrayList buf = new TIntArrayList();

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
            switch (state) {
                case 2:  // New node.
                    BRANCH[d] = -1;
                    if (tracing.contains(Trace.STEP))
                        log.trace("New node at level %d. BRANCH[%d] is %d.", d, d, BRANCH[d]);
                    ++nodeCount;
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
                        for (int i = 1; i <= N; ++i) sat[i - 1] = (var[i].VAL & 1) == 0;
                        return Optional.of(sat);
                    }
                    // Where we left off: Alg. X has returned with force data; we got here just after bumping d; we go off to state 5 without
                    // making an entry in the BACKF array for this level!!!!!

                    if (FORCE.size() > 0) {
                        if (tracing.contains(Trace.STEP)) log.trace("FORCE not empty, so going to step 5.", FORCE);
                        state = 5;
                        continue;
                    }
                    // /* explain why this is way down here */ BRANCH[d] = -1;
                    //BRANCH[d]=-1;//XXX
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
                        Literal top = null;
                        for (int i = 0; i < x.S; ++i) {
                            Literal cl = look[i].literal;
                            if (negated(cl.id)) continue;
                            double z = (cl.H + 0.1) * (cl.not.H  + 0.1);
                            if (tracing.contains(Trace.SCORE))
                                log.trace(" %s, %.4f:%.4f (%.4f)", cl, cl.H, cl.not.H, z);
                            if (z > maxz) {
                                maxz = z;
                                top = cl;
                            }
                        }
                        if (top == null) throw new IllegalStateException("unexpectedly no candidates but not SAT?");
                        else if (isfixed(top)) l = null;
                        else if (top.H > top.not.H) l = top.not;
                        else l = top;
                    } else l = neglit(VAR[0]); // trivial heuristic: deny the first free variable
                    if (l == null) {
                        if (tracing.contains(Trace.STEP))
                            log.trace("no branch at level %d; d becomes %d and going to step 2.", d, d + 1);
                        ++d;
                        state = 2;
                        continue;
                    }
                    if (tracing.contains(Trace.STEP))
                        log.trace("The search will continue with literal %s. Branch[%d] becomes 0.", l, d);
                    DEC[d] = l;
                    BACKF[d] = F;
                    BACKI[d] = ISTACKb.size();
                    BRANCH[d] = 0;
                }
                case 4:  // Try l.
                    if (tracing.contains(Trace.SEARCH)) {
                        log.trace("Level %d: Trying %s", d, l);
                    }
                    SIGL = d + 1;
                    FORCE.clear();
                    FORCE.add(l);
                case 5:  // Accept near truths.
                    if (tracing.contains(Trace.STEP)) log.trace("Accepting near-truths of %s.", FORCE);
                    T = NT;
                    G = E = F;
                    ++ISTAMP;
                    // Perform the binary propagation routine (62) for all the literals in FORCE
                    for (int i = 0; i < FORCE.size(); ++i) { // int f : FORCE) { removed since allocation is done
                        if (!propagate(FORCE.get(i))) {
                            state = 11;
                            continue STEP;
                        }
                    }
                    FORCE.clear();

                case 6: { // Choose a nearly true l.
                    if (G == E) {
                        state = 10;
                        continue;
                    }
                    Literal L = R[G];
                    ++G;
                    // case 7:  Promote L to real truth.
                    if (tracing.contains(Trace.STEP)) log.trace("Promote %s to real truth", L);

                    // TODO: fix types here.
                    Variable X = L.var;
                    X.VAL = RT + (L.id & 1);  // TODO magic number
                    // Remove variable X from the free list and from all TIMP pairs (ex. 137).
                    final int N1 = N - G;
                    Variable x = VAR[N1];
                    int j = X.INX;
                    VAR[j] = x;
                    x.INX = j;
                    VAR[N1] = X;
                    X.INX = N1;
                    for (int xlit = poslit(X).id; xlit <= neglit(X).id; ++xlit) {
                        for (int p = lit[xlit].TIMP, tcount = 0; tcount < lit[xlit].TSIZE; p = NEXT.get(p), ++tcount) {
                            int u0 = U.get(p);
                            int v = V.get(p);
                            int pp = LINK.get(p);
                            int ppp = LINK.get(pp);
                            int s = lit[not(u0)].TSIZE - 1;
                            if (s < 0 || s > 999999) throw new IllegalStateException("susp. A " + s);
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
                            s = lit[not(v)].TSIZE - 1;
                            if (s < 0 || s > 999999) throw new IllegalStateException("susp. B " + s);
                            lit[not(v)].TSIZE = s;
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
                    for (int p = L.TIMP, tcount = 0; tcount < L.TSIZE; p = NEXT.get(p), ++tcount) {
                        // TODO: type of U, V
                        final int u = U.get(p), v = V.get(p);
                        if (tracing.contains(Trace.FIXING)) log.trace("  %s->%s|%s", L, u, v);
                        if (!consider(lit[u], lit[v])) {
                            state = 11;
                            continue STEP;
                        }
                    }
                    state = 6;
                    continue;
                }
                /* Steps 8 and 9 are in the method consider(). */
                case 10:  // Accept real truths.
                    if (tracing.contains(Trace.FIXING))
                        log.trace("state 10 E=%d F=%d BRANCH[%d]=%d", E, F, d, BRANCH[d]);
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
                        R[E].var.VAL = 0;
                    }
                case 12:  // Unfix real truths.
                    while (E > F) {
                        --E;
                        Variable X = R[E].var;
                        // reactivate the TIMP pairs that involve X and restore X to the free list (ex. 137)
                        for (int xlit = 2 * X.id + 1; xlit >= 2 * X.id; --xlit) {
                            if (tracing.contains(Trace.BIMP)) log.trace("Reactivating %d", dl(xlit));
                            // Knuth insists (in the printed fascicle) that the downdating of TIMP should
                            // happen in the reverse order of the updating, which would seem to argue for
                            // traversing this linked list in reverse order. However, since each entry in
                            // the TIMP list will point (via U and V) to two strictly other TIMP lists, it's
                            // not clear why the order matters.

                            buf.resetQuick();

                            for (int p = lit[xlit].TIMP, tcount = 0; tcount < lit[xlit].TSIZE; p = NEXT.get(p), ++tcount)
                                buf.add(p);
                            buf.forEachDescending(p -> {
                                ++lit[not(U.get(p))].TSIZE;
                                ++lit[not(V.get(p))].TSIZE;
                                return true;
                            });
                        }
                        X.VAL = 0;
                    }
                case 13:  // Downdate BIMPs
                    if (BRANCH[d] >= 0) {
                        while (ISTACKb.size() > BACKI[d]) {
                            ISTACKb.pop().BSIZE = ISTACKs.pop();
                        }
                    }
                case 14:  // Try again?
                    if (BRANCH[d] == 0) {
                        // Move to branch 1.  Add a 1 bit to the binary prefix string, unless it is already long enough.
                        // We don't add zero bits at branch zero. Instead, the prefix starts out at zero, and 1-bits are
                        // retracted at backtrack time, so we don't need to push 0-bits into the prefix.
                        if (d < 32) SIG |= 1 << (31 - d);
                        l = DEC[d];
                        DEC[d] = l = l.not;
                        BRANCH[d] = 1;
                        if (tracing.contains(Trace.SEARCH)) log.trace("d=%d. That didn't work, trying %s", d, l);
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
                    if (d < 31) SIG &= -(1 << (31 - d));  // Remove a bit from the binary prefix string
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
        private final ArrayList<Variable> CAND = new ArrayList<>();  // candidate variables for algorithm X
        private final Literal[] CANDL;  // candidate literals for algorithm X

        final float alpha = 3.5f;
        final float THETA = 20.0f;
        final int C0 = 30, C1 = 600;  // See Ex. 148
        final int nVariables;
        private Literal l0;  // Current lookahead literal (used in algorithm X)
        int S;  // number of candidate literals
        private double w = 0.0;  // Current weight of lookahead choice. TODO it is dodgy that this is an instance variable...
        private final float[][] h;  // h[d][l] is the h-score ("rough heuristic") of literal l at depth d

        AlgorithmX() {
            nVariables = problem.nVariables();
            h = new float[nVariables + 1][];
            CANDL = new Literal[2 * nVariables];
        }

        float[] computeHeuristics() {
            final int N = nVariables - F;

            if (h[d] == null) {
                h[d] = new float[2 * nVariables + 2];
            }
            if (d <= 1) Arrays.fill(h[d], 1);
            else System.arraycopy(h[d - 1], 0, h[d], 0, h[d].length);
            float[] hd = h[d];
            int nCycles = d <= 1 ? 5 : 1;

            // Step X1 is performed before this routine is called.
            // Step X2: Compile rough heuristics.
            float sum, tsum, factor, sqfactor, afactor;

            for (int k = 0; k < nCycles; ++k) {
                sum = 0;
                for (int i = 0; i < N; ++i) {
                    final Variable v = VAR[i];
                    sum += hd[poslit(v).id] + hd[neglit(v).id];
                }
                factor = 2f * N / sum;
                sqfactor = factor * factor;
                afactor = alpha * factor;
                // TODO: this allocation needs to be killed; use Knuth's technique of alternating between two static arrays.
                float[] hprime = new float[hd.length];
                for (int i = 0; i < N; ++i) {
                    final Variable v = VAR[i];
                    for (int l = poslit(v).id; l <= neglit(v).id; ++l) {
                        int bcount = 0, tcount = 0;  // XXX
                        sum = 0;
                        // for all u in BIMP[l] with u not fixed
                        List<Literal> bimpl = lit[l].BIMP;
                        for (int j = 0; j < lit[l].BSIZE; ++j) {
                            final Literal u = bimpl.get(j);  // TODO: name, type
                            if (isfree(u)) {
                                ++bcount;
                                // TODO: hmm.
                                sum += hd[u.id];
                            }
                        }
                        tsum = 0;
                        for (int p = lit[l].TIMP, j = 0; j < lit[l].TSIZE; p = NEXT.get(p), ++j) {
                            tsum += hd[U.getQuick(p)] * hd[V.getQuick(p)];
                            ++tcount;
                        }
                        sum = 0.1f + sum * afactor + tsum * sqfactor;
                        if (l >= 6 && l <= 12)
                            log.trace("L=%d sum=%.6f b%d/t%d TSIZE=%d", l, sum, bcount, tcount, lit[l].TSIZE);
                        hprime[l] = Float.min(THETA, sum);
                        // if (tracing.contains(Trace.SCORE)) log.trace("h[%s] = %.4f", lit[l], hprime[l]);
                    }
                }
                System.arraycopy(hprime, 2, hd, 2, 2 * nVariables);
            }
            return hd;
        }

        float[] computeHeuristicsORIG() {
            final int N = nVariables - F;

            if (h[d] == null) {
                h[d] = new float[2 * nVariables + 2];
                if (d <= 1) Arrays.fill(h[d], 1);
                else System.arraycopy(h[d - 1], 0, h[d], 0, h[d].length);
            }
            float[] hd = h[d];
            int nCycles = d <= 1 ? 5 : 1;

            // Step X1 is performed before this routine is called.
            // Step X2: Compile rough heuristics.
            for (int k = 0; k < nCycles; ++k) {
                double hAve = 0.0;
                for (int i = 0; i < N; ++i) {
                    final Variable v = VAR[i];
                    hAve += hd[poslit(v).id] + hd[neglit(v).id];
                }
                hAve /= 2.0 * N;
                final double hAve2 = hAve * hAve;
                // TODO: this allocation needs to be killed; use Knuth's technique of alternating between two static arrays.
                float[] hprime = new float[hd.length];
                for (int i = 0; i < N; ++i) {
                    final Variable v = VAR[i];
                    // TODO: subroutinize the following and unroll this loop.
                    for (int l = poslit(v).id; l <= neglit(v).id; ++l) {
                        // update hd[l]
                        float hp = 0.1f;
                        // for all u in BIMP[l] with u not fixed
                        List<Literal> bimpl = lit[l].BIMP;
                        float hs = 0;
                        for (int j = 0; j < lit[l].BSIZE; ++j) {
                            final Literal L = bimpl.get(j);
                            if (isfree(L)) hs += hd[L.id];
                        }
                        hp += alpha * hs / hAve;
                        hs = 0;
                        for (int p = lit[l].TIMP, j = 0; j < lit[l].TSIZE; p = NEXT.get(p), ++j) {
                            hs += hd[U.get(p)] * hd[V.get(p)];
                        }
                        hp += hs / hAve2;
                        hprime[l] = Float.min(THETA, hp);
                        // if (tracing.contains(Trace.SCORE)) log.trace("h[%s] = %.4f", lit[l], hprime[l]);
                    }
                }
                System.arraycopy(hprime, 2, hd, 2, 2 * nVariables);
            }
            return hd;
        }

        /*
         * Put free variables into the CAND array. If participantsOnly, be sure to only admit variables which
         * are participants.
         */
        private void selectCandidates(boolean participantsOnly) {
            CAND.clear();
            for (int i = 0; i < nVariables - F; ++i) {
                final Variable v = VAR[i];
                v.VAL = 0;  // erase all former assignments
                if (participantsOnly) {
                    // Perform the prefix test. Skip to next free variable if it fails.
                    // Knuth sat11: if (x > primary_vars) continue;
                    final int t = v.SIG, l = v.SIGL;
                    if (l == SIGL) {
                        if (t != SIG) continue;  // not a candidate. simple comparison since lengths are the same.
                    } else if (l > SIGL) continue;  // v's signature is too long to be a prefix of the current signature
                    else if (t != (l < 32 ? SIG & -(1 << (32 - l)) : SIG)) continue;  // prefixes don't match
                }
                if (tracing.contains(Trace.FOREST)) log.trace("adjoining candidate %s", v);
                CAND.add(v);
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
            final float[] hd = computeHeuristics();
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
                VARIABLE:
                for (int vi = 0; vi < nVariables - F; ++vi) {
                    final Variable v = VAR[vi];
                    for (int l = poslit(v).id; l <= neglit(v).id; ++l) {
                        // l is a free literal since v is a free variable.
                        if (lit[l].TSIZE > 0) {
                            sat = false;
                            break VARIABLE;
                        }
                        List<Literal> bimpl = lit[l].BIMP;
                        for (int j = 0; j < lit[l].BSIZE; ++j) {
                            if (fixity(bimpl.get(j)) == Fixity.UNFIXED) {
                                sat = false;
                                break VARIABLE;
                            }
                        }
                    }
                }
                if (sat) log.warn("X found SAT, but we're pretending we didn't. F=%d / N=%d", F, nVariables);
                // TODO: figure out how to communicate SAT found to upper level!
                // Otherwise, if we didn't get lucky, add candidates non-selectively.
                selectCandidates(false);
            }

            // Give each free variable the rating h(x)h(¬x)
            for (int i = 0; i < N; ++i) {
                final Variable v = VAR[i];
                v.rating = hd[poslit(v).id] * hd[neglit(v).id];
            }

            if (tracing.contains(Trace.SCORE)) {
                for (int v = 0; v < nVariables; ++v) {
                    log.trace("rating[%9d] = %8.4f   == %8.4f * %8.4f", v, var[v].rating, hd[poslit(v)], hd[neglit(v)]);
                }
            }

            final double C_max = d == 0 ? C1 : Integer.max(C0, C1 / d);  // Eq. (66)

            if (tracing.contains(Trace.SCORE)) log.trace("C_max = %g", C_max);

            double r_sum = 0.;
            for (int i = 0; i < CAND.size(); ++i) {
                r_sum += CAND.get(i).rating;
            }

            // While C > 2 C_max, delete all elements of CAND whose rating
            // is less than the mean rating; but terminate the loop if no elements are
            // actually deleted.


            while (CAND.size() > 2 * C_max) {
                // Compute the mean score.
                final int sz = CAND.size();
                double r_mean = r_sum / sz;
                int back = CAND.size();
                r_sum = 0.0;
                for (int i = 0; i < back; ) {
                    final double score = CAND.get(i).rating;
                    if (score < r_mean) {
                        // This is a bad one. Pull a new one from the end of the candidates list.
                        CAND.set(i, CAND.get(--back));
                    } else {
                        // This is a good one. Keep it, accumulate its score, and go to the next.
                        r_sum += score;
                        ++i;
                    }
                }
                if (back == CAND.size()) break;  // nothing was removed
                else CAND.subList(back, CAND.size() - back).clear();
            }
            // Finally, if C > C_max, reduce C to C_max by retaining only top-ranked
            // candidates.
            if (CAND.size() > C_max) {
                // Here's an allocation. Maybe we want to put heapification under
                // user control. Can we also close over var[] that way... XXX
                Heap<Variable> h = new Heap<>();  // TODO: move
                h.heapify(CAND);
                while (CAND.size() > C_max) h.pop();
            }

            ++BSTAMP;
            // Mark surviving candidates with the new BSTAMP value, and compute big H with equation (67).
            log.trace("there are %d candidate variables", CAND.size());
            print();
            for (int i = 0; i < CAND.size(); ++i) {
                final Variable c = CAND.get(i);
                for (int candlit = 2 * c.id; candlit <= 2 * c.id + 1; ++candlit) {
                    final Literal l = lit[candlit];
                    l.bstamp = BSTAMP;
                    l.arcs.clear();
                    l.H = 0;
//                    for (int j = l.TIMP, k = 0; k < l.TSIZE; j = NEXT.getQuick(j), ++k) {
//                        //System.out.printf("%d => %d and %d\n", dl(l), dl(U.getQuick(j)), dl(V.getQuick(j)));
//                        // WHERE WE LEFT OFF:
//                        // I have the weird sensation this is being done twice for some reason.
//                        // It's almost as if H is being conflated with something else, or we haven't
//                        // read the doc attentively enough.
//
//                        // QQ: if not for this, would the numbers add up?
//
//                        H[candlit] += hd[U.getQuick(j)] * hd[V.getQuick(j)];
//                    }
                }
            }
            S = 0;
            // Compute candidate BIMP list.
            for (int i = 0; i < CAND.size(); ++i) {
                final Variable c = CAND.get(i);
                for (int candlit = poslit(c).id; candlit <= neglit(c).id; ++candlit) {
                    final Literal u = lit[candlit];
                    log.trace("considering: %s (bsize=%d, bimp size=%d) table = %s", u, u.BSIZE, u.BIMP.size(), u.BIMP);
                    CANDL[S++] = u;
                    u.vcomp = u;  // A field we will use after resolving into strong components
                    List<Literal> bimp = u.BIMP;
                    for (int j = 0; j < u.BSIZE; ++j) {
                        Literal v = bimp.get(j);
                        if (v.id > candlit && v.bstamp == BSTAMP) {
                            // Knuth: we add v --> u to the candidate arcs when there's an implication u => v in the BIMP table.
                            // We also add the arc ¬v --> ¬u. By enforcing v > candlit, we ensure that both directions are added
                            // atomically (the BIMP table contains both arrows, but not contiguously; if we are going to cap
                            // the number of arcs we consider, it is important that we don't strand one arc of a pair outside
                            // the graph).
                            log.trace("arc for %d: %s -> %d, %d -> %s", dl(candlit), v, dl(candlit), dl(not(candlit)), v.not);
                            v.arcs.add(u);
                            u.not.arcs.add(v.not);  // TODO: type of v.
                        }
                    }
                }
            }

            // One Weird Trick: do we need to reverse the order of the arcs to get our components out in the right
            // order?
            if (knuthCompatible) for (int i = 0; i < S; ++i) Collections.reverse(CANDL[i].arcs);

            for (int i = 0; i < S; ++i) {
                Literal l = CANDL[i];
                if (!l.arcs.isEmpty()) log.trace("Arcs: %s -> %s", l, l.arcs);
            }

            // X4 [Nest the candidates.]

            ConnectedComponents cc = new ConnectedComponents();
            cc.find(CANDL, S);


            // TODO: Knuth's Tarjan algorithm is modified to notice when ~v lives in v's SCC.
            // Our implementation does not notice this, but it would be easy to check, for
            // all literals among the candidates, that


            // Rip over the components, finding, within each, the literal of maximum rating
            // (this is used as an alternate component representative.) We also check here
            // to see if a component contains a literal contradictory to its CC representative.

            for (int i = 0; i < S; ++i) {
                final Literal l = CANDL[i];
                // TODO: consider equipping literals with a pointer to their variable parents
                if (l != l.parent && var[thevar(l.id)].rating > var[thevar(l.parent.vcomp.id)].rating) {
                    l.parent.vcomp = l;
                }
                if (l.id == not(l.parent.id)) {
                    if (tracing.contains(Trace.LOOKAHEAD)) log.trace("contradiction discovered in lookahead");
                    return false;
                }
            }

            if (tracing.contains(Trace.FOREST)) {
                log.trace("Strong components:");
                for (Literal s = cc.settled(); s != null; s = s.link) {
                    final Literal t = s;
                    log.trace(() -> {
                        StringBuilder sb = new StringBuilder(String.format(" %d %.4g", dl(t.id), var[thevar(t.id)].rating));
                        if (t.parent != t) sb.append(" with ").append(dl(t.parent.id));
                        else if (t.vcomp != t)
                            sb.append("-> ").append(dl(t.vcomp.id)).append(String.format(" %.4g", var[t.vcomp.id >> 1].rating));
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
                    List<Literal> arcs = u.not.arcs;
                    // log.trace("arcs = " + Arrays.stream(arcs.toArray()).mapToObj(a -> lit[a].toString()).collect(Collectors.joining(",")));
                    for (int j = 0; j < arcs.size(); ++j) {
                        Literal v = arcs.get(j).not;
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

            if (tracing.contains(Trace.FOREST)) for (Literal l : CANDL) {
                log.trace("  %d: height %d, child %s, link %s", dl(l.id), l.height,
                        l.child != null ? dl(l.child.id) : 0,
                        l.link != null ? dl(l.link.id) : 0);
            }

            // Construct a sequence of literals LL[j] and corresponding truth offsets LO[j], for 0 <= j < S.
            // This is the "lookahead forest."

            int looks = 0;
            {
                int j = 0;
                Literal u = root.child, v = null;
                LOOK:
                while (true) {
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

            STEP:
            while (true) {
                //System.out.printf("X in state %d. j = %d\n", xstate, j);
                switch (xstate) {
                    case 6: { // [Choose l for lookahead.]
                        l = look[j].literal;
                        T = BASE + look[j].offset;
                        if (l.parent != null) {
                            log.trace("WNB for %s is being inherited from parent %s: %.4f overwrites %.4f", l, l.parent, l.parent.H, l.H);
                            l.H = l.parent.H;
                        }
                        if (tracing.contains(Trace.LOOKAHEAD))
                            log.trace("looking at %s @%d H=%.4g", l, T, l.H);

                        // TODO: type of l
                        Fixity f = fixity(l);
                        if (f == Fixity.UNFIXED) {
                            xstate = 8;
                            continue;
                        }
                        if (f == Fixity.FIXED_F && l.var.VAL < PT) {
                            if (!X12(l.not)) {
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
                        xstate = 6;
                        continue;
                    case 8: { // [Compute sharper heuristic.]
                        //System.out.printf("now state 8...\n");
                        if (!Perform72()) {
                            xstate = 13;
                            continue;
                        }
                        // Then...
                        if (w > 0) {
                            l0.H += w;
                            log.trace("** now H[%s] = %.4f after adding %.4f", l0, l0.H, w);
                            xstate = 10;
                            continue;
                        }
                    }
                    case 9:  // [Exploit an autarky.]
                        if (l0.H == 0) {
                            if (tracing.contains(Trace.LOOKAHEAD)) log.trace("autarky (a) at %s\n", l0);
                            if (!X12(l0)) {
                                xstate = 13;
                                continue;
                            }
                        } else {
                            // TODO: change l0 to a Literal, or at least cache the value of lit[l0]
                            if (tracing.contains(Trace.LOOKAHEAD)) log.trace("autarky (b) at %s", l0);
                            // Generate the binary clause l0 | ~PARENT(l0)
                            appendToBimp(l0.not, l0.parent.not);
                            appendToBimp(l0.parent, l0);
                        }
                    case 10:  // [Optionally look deeper.]
                    case 11:  // [Exploit necessary assignments.]
                        // TODO: type of l0
                        List<Literal> bimp = l0.not.BIMP;
                        for (int i = 0; i < l0.not.BSIZE; ++i) {
                            Literal u = bimp.get(i);
                            Fixity f = fixity(u);
                            if (f == Fixity.FIXED_T && u.var.VAL < PT) X12(u);
                        }
                        xstate = 7;
                        continue;
                    case 13:  // [Recover from conflict.]
                        if (tracing.contains(Trace.LOOKAHEAD)) log.trace("lookahead conflict at %s", l0);
                        if (T < PT) {
                            l = l0.not;
                            if (!X12(l)) {
                                return false;
                            }
                            xstate = 7;
                            continue;
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
            // TODO: get rid of this allocation
            List<Literal> W = new ArrayList<>();
            // log.trace("%sfixing %d", tName(T), dl(l));
            if (!propagate(l)) return false;  // Perform (62).
            while (G < E) {
                Literal L = R[G];
                ++G;
                // take account of (u, v) for all (u, v) in TIMP(L)
                for (int t = 0, p = L.TIMP; t < L.TSIZE; ++t, p = NEXT.getQuick(p)) {
                    Literal u = lit[U.getQuick(p)], v = lit[V.getQuick(p)];
                    if (tracing.contains(Trace.FIXING)) log.trace("  looking %s->%s|%s", L, u, v);
                    Fixity fu = fixity(u), fv = fixity(v);
                    if (fu == Fixity.FIXED_T || fv == Fixity.FIXED_T) continue;
                    if (fu == Fixity.FIXED_F && fv == Fixity.FIXED_F) {
                        if (tracing.contains(Trace.FIXING)) log.trace("P72 contradiction: both fixed false");
                        return false;
                    }
                    if (fu == Fixity.FIXED_F && fv == Fixity.UNFIXED) {
                        if (!propagate(v)) {
                            if (tracing.contains(Trace.FIXING))
                                log.trace("P72 contradiction: failed to propagate %s", v);
                            return false;
                        }
                        W.add(v);
                    } else if (fu == Fixity.UNFIXED && fv == Fixity.FIXED_F) {
                        if (!propagate(u)) {
                            if (tracing.contains(Trace.FIXING))
                                log.trace("P72 contradiction: failed to propagate %s", u);
                            return false;
                        }
                        W.add(u);
                    } else {
                        assert fu == Fixity.UNFIXED && fv == Fixity.UNFIXED;
                        w += h[d][u.id] * h[d][v.id];
                        log.trace("WNB += [%s:]%.4f * [%s:]%.4f = %.4f ---> %.4f",
                                u, h[d][u.id],
                                v, h[d][v.id],
                                h[d][u.id] * h[d][v.id],
                                w);
                    }
                }
                // generate new binary clauses (lbar_0 | w) for w in W.
                for (int i = 0; i < W.size(); ++i) {
                    Literal w = W.get(i);
                    // TODO: fix type
                    if (tracing.contains(Trace.LOOKAHEAD)) log.trace("windfall %s->%s", l0, w);
                    appendToBimp(l0, w);
                    appendToBimp(w.not, l0.not);
                }
                // Through with the windfalls.
                W.clear();
            }
            return true;
        }

        boolean X12(Literal l) {
            if (tracing.contains(Trace.LOOKAHEAD)) log.trace("forcing %s", l);
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

    private Literal poslit(Variable v) { return lit[poslit(v.id)]; }
    private Literal neglit(Variable v) { return lit[neglit(v.id)]; }
    private boolean isfree(Literal l) {
        return l.var.VAL < RT;
    }
    private boolean isfixed(Literal l) {
        return l.var.VAL >= RT;
    }
}
