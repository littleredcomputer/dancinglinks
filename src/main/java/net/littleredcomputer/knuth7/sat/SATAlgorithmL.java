package net.littleredcomputer.knuth7.sat;

import com.google.common.collect.Lists;
import gnu.trove.list.array.TIntArrayList;
import gnu.trove.stack.TIntStack;
import gnu.trove.stack.array.TIntArrayStack;
import net.littleredcomputer.knuth7.SGBRandom;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import javax.annotation.CheckReturnValue;
import javax.annotation.Nonnull;
import java.util.*;
import java.util.stream.Collectors;

public abstract class SATAlgorithmL extends AbstractSATSolver {
    private static final Logger log = LogManager.getFormatterLogger();
    private static final int RT = 0x7ffffffe;
    private static final int NT = RT - 2;
    private static final int PT = NT - 2;

    abstract void addClause(List<Integer> clause);
    abstract void printTable();
    abstract boolean deactivate(Literal L);
    abstract void reactivate(Literal L);
    abstract float[] computeHeuristics();
    abstract boolean Perform72(Literal l);
    abstract boolean Perform73(Literal l);
    abstract void ResetFptr();  // TODO this is dodgy

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
        @Override public int compareTo(@Nonnull Variable o) { return Float.compare(rating, o.rating); }
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
        final List<Literal> BIMP = new ArrayList<>();
        TIntArrayList KINX;  // list of wide clause indices containing this literal
        int KSIZE = 0;  // current count of active wide clauses containing this literal

        // auxiliary data for Tarjan's algorithm
        long bstamp = 0;  // bstamp value identifies current generation of candidates
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
        Literal child;
        int height;
        float H;  // the "refined" heuristic score
        long DFAIL = 0;  // used in Algorithm Y

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

    static class Lookahead {
        Literal LL = null;
        int LO = 0;
    }

    final int nVariables;
    private final List<Literal> FORCE = new ArrayList<>();
    final Literal[] lit;
    final boolean wide;  // true if there is a clause with more than 3 literals
    // TODO: add a comment explaining the difference between these and probably change the name of one of them.
    private final Variable[] var;
    final Variable[] VAR;
    private final Literal[] DEC;
    private final int[] BACKF;  // backtrack value of F, indexed by depth
    private final int[] BACKI;  // backtrack value of ISTACK size, indexed by depth
    private final int[] BRANCH;
    final Literal[] R;  // stack of literals
    // Reading Knuth we might choose to implement ISTACK as a stack of pairs of ints. But that would require boxing.
    // Instead, we use a pair of stacks.
    private final Deque<Literal> ISTACKb = new ArrayDeque<>();  // stack of literals
    private final TIntStack ISTACKs = new TIntArrayStack();  // stack of BIMP table sizes for corresponding literals above
    private int T = NT;  // truth degree (F6 7.2.2.2 p. 37)
    int E = 0;  // literals R[k] are "nearly true" for G <= k < E.
    int F = 0;
    int G = 0;
    private long ISTAMP = 0;  // Knuth points out (sat11.w:1528) that this could conceivably overflow a 32-bit int
    private long BSTAMP = 0;  // stamp value of current candidate list in algorithm X
    int d = 0;  // current depth within search tree
    // private int state = 2;  // currently executing step of algorithm L
    // private Literal l = null;  // Current branch literal
    private int SIG = 0;  // Current prefix of binary encoding of branch state
    private int SIGL = 0;
    private final List<Literal> track = new ArrayList<>();  // used to record linear branch sequence, for test purposes
    boolean trackChoices = false;  // if true, track array will be filled during search for testing; otherwise not
    double w = 0.0;  // Current weight of lookahead choice. TODO it is dodgy that this is an instance variable...


    boolean useX = true;  // whether to use algorithm X for lookahead
    boolean useY = true;  // whether to use algorithm Y for double-lookahead
    private final boolean knuthCompatible = true;
    final Deque<Literal> W = new ArrayDeque<>();  // windfalls

    enum Trace {STEP, SEARCH, LOOKAHEAD, BIMP, SCORE, FIXING, FOREST}
    EnumSet<Trace> tracing = EnumSet.noneOf(Trace.class);
    private AlgorithmX x = null;

    private enum Result {
        LOOKAHEAD,  // We have filled the table of lookahead heuristics. Pick a branch!
        UNSAT,      // We have proven that the problem is unsatisfiable
        SAT         // We have found a satisying (possibly partial) assignment
    }

    enum Fixity {
        UNFIXED,
        FIXED_T,
        FIXED_F
    }

    public static SATAlgorithmL New(SATProblem p) {
        if (p.width() <= 3) return new SATAlgorithmL3(p);
        return new SATAlgorithmLX(p);
    }

    SATAlgorithmL(String name, SATProblem p) {
        super(name, p);
        nVariables = problem.nVariables();
        var = new Variable[nVariables + 1];
        wide = p.width() > 3;

        Arrays.setAll(var, Variable::new);
        lit = new Literal[2 * nVariables + 2];
        Arrays.setAll(lit, Literal::new);
        for (Literal l : lit) {
            l.not = lit[not(l.id)];
            l.var = var[thevar(l.id)];
            l.KINX = new TIntArrayList();
        }
        VAR = new Variable[nVariables];
        DEC = new Literal[nVariables];
        BACKF = new int[nVariables];
        BACKI = new int[nVariables];
        BRANCH = new int[nVariables + 1];
        R = new Literal[nVariables + 1];  // stack to record the names of literals that have received values.
        // A literal and its complement never appear together here, so nVariables is enough space (but: one-based)

        // We process the clauses in reverse order because Knuth does. This means our BIMP and TIMP tableaux
        // will be initialized with the same data in the same order as sat11.w.

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
    }

    void addClauses() {
        Set<Integer> units = new HashSet<>();
        List<Set<Integer>> oBIMP = new ArrayList<>(2*nVariables+2);
        for (int i = 0; i < 2 * nVariables + 2; ++i) oBIMP.add(new HashSet<>());
        Lists.reverse(problem.encodedClauses()).forEach(clause -> {
            switch (clause.size()) {
                case 1: {
                    // Put it in the FORCE array, unless it is contradictory
                    final int u = clause.get(0);
                    if (units.contains(not(u)))
                        throw new IllegalArgumentException("Contradictory unit clauses involving variable " + thevar(u) + " found");
                    units.add(u);
                    break;
                }
                case 2: {
                    // Put it in the BIMP. Choosing v, u in this order produces a Knuth-compatible BIMP table.
                    final int v = clause.get(0), u = clause.get(1);
                    oBIMP.get(not(u)).add(v);
                    oBIMP.get(not(v)).add(u);
                    break;
                }
                default:
                    addClause(clause);
            }
        });
        for (int li = 2; li < 2 * nVariables + 2; ++li) {
            final Literal l = lit[li];
            oBIMP.get(li).forEach(i -> l.BIMP.add(lit[i]));
            l.BSIZE = l.BIMP.size();
        }
        units.forEach(i -> FORCE.add(lit[i]));
        if (!FORCE.isEmpty() && tracing.contains(Trace.SEARCH)) log.trace("initially forcing %s", FORCE);

    }

    /**
     * Propagate the literal l through all of the binary clauses using the BIMP table.
     * If a conflict is at any point, the propagation is abandoned early and false is
     * returned.
     */
    @CheckReturnValue
    boolean propagate(Literal l) {
        int H = E;
        if (!takeAccountOf(l, false)) {
            return false;
        }
        for (; H < E; ++H) {
            List<Literal> bimpl = R[H].BIMP;
            for (int i = 0; i < R[H].BSIZE; ++i) {
                if (!takeAccountOf(bimpl.get(i), true)) return false;
            }
        }
        return true;
    }

    /**
     * Implements equation (62) of 7.2.2.2. Returns false if the next step is CONFLICT.
     */
    @CheckReturnValue
    private boolean takeAccountOf(Literal l, boolean subordinate) {
        switch (fixity(l)) {
            case FIXED_T: return true;
            case FIXED_F: return false; /* conflict */
            case UNFIXED:
                if (tracing.contains(Trace.FIXING)) log.trace("%s%sfixing %s", subordinate ? " " : "", truthName(T), l);
                l.var.VAL = T + (l.id & 1);
                R[E++] = l;
        }
        return true;
    }

    /* Append l to BIMP[b], allowing for an undo in the future. */
    void appendToBimp(Literal b, Literal l) {
        final int bsize = b.BSIZE;
        if (b.IST != ISTAMP) {
            b.IST = ISTAMP;
            ISTACKb.push(b);
            ISTACKs.push(bsize);
        }
        List<Literal> bimp = b.BIMP;
        if (bimp.size() > bsize) bimp.set(bsize, l);
        else if (bimp.size() == bsize) bimp.add(l);
        else throw new IllegalStateException("bimp size invariant violation");
        ++b.BSIZE;
    }

    void makeParticipant(Variable v) {
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
    @CheckReturnValue
    boolean consider(Literal u, Literal v) {
        // if (log.isTraceEnabled()) log.trace("consider %d∨%d", dl(u), dl(v));
        // STEP L8: Consider u ∨ v
        Fixity fu = fixity(u);
        Fixity fv = fixity(v);

        if (fu == Fixity.FIXED_T || fv == Fixity.FIXED_T) return true;
        else if (fu == Fixity.FIXED_F && fv == Fixity.FIXED_F) return false;
        else if (fu == Fixity.FIXED_F && fv == Fixity.UNFIXED) return propagate(v);
        else if (fv == Fixity.FIXED_F && fu == Fixity.UNFIXED) return propagate(u);
        return newBinaryClause(u, v);
    }

    /**
     * STEP L9: update for a new binary clause u | v.
     */
    @CheckReturnValue
    private boolean newBinaryClause(Literal u, Literal v) {
        ++BSTAMP;
        final Literal ubar = u.not, vbar = v.not;
        ubar.bstamp = BSTAMP;
        for (int i = 0; i < ubar.BSIZE; ++i) ubar.BIMP.get(i).bstamp = BSTAMP;
        if (vbar.bstamp == BSTAMP) {
            /* we already have u | ~v */
            /* fix_u: */ return propagate(u);
        } else if (v.bstamp != BSTAMP) {
            /* we don't have u | v */
            /* "...but goto fix_u if u is forced true" */
            if (!addCompensationResolventsFrom(u, v)) return propagate(u);
            ++BSTAMP;
            vbar.bstamp = BSTAMP;
            for (int i = 0; i < vbar.BSIZE; ++i) vbar.BIMP.get(i).bstamp = BSTAMP;
            if (ubar.bstamp == BSTAMP) {
                /* we already have ~u | v */
                /* fix_v: */ return propagate(v);
            } else {
                /* but goto fix_v if if v is forced true */
                if (!addCompensationResolventsFrom(v, u)) return propagate(v);
                appendToBimp(ubar, v);  // ~u => v
                appendToBimp(vbar, u);  // ~v => u
            }
        }
        return true;
    }

    @CheckReturnValue
    private boolean addCompensationResolventsFrom(Literal u, Literal v) {
        for (int i = 0; i < v.BSIZE; ++i) {
            final Literal w = v.BIMP.get(i);
            if (!isfixed(w)) {
                if (w.not.bstamp == BSTAMP) {
                    return false; /* goto fix_u or fix_v */
                }
                if (w.bstamp != BSTAMP) { /* u | w is new */
                    if (tracing.contains(Trace.FIXING)) log.trace(" K -> %s|%s", u, w);
                    appendToBimp(u.not, w); /* ~u => w */
                    appendToBimp(w.not, u); /* ~w => u */
                }
            }
        }
        return true;
    }

    /* Returns the fixity of l in the context T */
    Fixity fixity(Literal l) {
        int val = l.var.VAL;
        if (val < T) return Fixity.UNFIXED;
        return negated(val) == negated(l.id) ? Fixity.FIXED_T : Fixity.FIXED_F;
    }

    private void print() {
        final boolean withExcess = false;
        log.trace("BIMP tables:");
        for (int i = 1; i < lit.length; ++i) {
            final Literal l = lit[i];
            final int bsize = l.BSIZE;
            if (bsize < 0) throw new IllegalStateException(String.format("bad BIMP at %s (%d)", l, bsize));
            if (bsize > 0) {
                log.trace("  %3s: %s %s",
                        l,
                        l.BIMP.stream().limit(bsize).map(Literal::toString).collect(Collectors.joining(" ")),
                        withExcess && (l.BSIZE < l.BIMP.size()) ? String.format("(+%d)", l.BIMP.size() - l.BSIZE) : "");
            }
        }

        printTable();
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
        Literal l = null;
        int state = 2;


        STEP:
        while (true) {
            ++stepCount;
            if (stepCount % logCheckSteps == 0) {
                maybeReportProgress(this::stateToString);
            }
            switch (state) {
                case 2:  // New node.
                    BRANCH[d] = -1;
                    if (tracing.contains(Trace.SEARCH))
                        log.trace("New node at level %d. BRANCH[%d] is %d.", d, d, BRANCH[d]);
                    if (tracing.contains(Trace.BIMP)) print();
                    ++nodeCount;
                    if (FORCE.isEmpty() && F < N && useX) {
                        switch (x.X()) {
                            case UNSAT:
                                if (tracing.contains(Trace.STEP)) log.trace("Alg. X detected a contradiction");
                                state = 15;
                                continue;
                            case SAT:
                                log.info("!SAT!");
                                return solution();
                        }
                    }
                    // Step X1:  Satisfied?
                    if (F == N) {
                        log.info("!SAT!");
                        return solution();
                    }
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
                            Literal cl = x.look[i].LL;
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
                        else if (!isfree(top)) l = null;
                        else if (top.H > top.not.H) l = top.not;
                        else l = top;
                    } else l = neglit(VAR[0]); // trivial heuristic: deny the first free variable
                    BACKF[d] = F;
                    BACKI[d] = ISTACKb.size();
                    if (l == null) {
                        if (trackChoices) track.add(l);
                        if (tracing.contains(Trace.STEP))
                            log.trace("no branch at level %d; d becomes %d and going to step 2.", d, d + 1);
                        ++d;
                        // knuth sets forcedlits=0 here... should we do the same?
                        if (FORCE.size() > 0) throw new IllegalStateException("how did we get here?");
                        state = 2;
                        continue;
                    }
                    if (tracing.contains(Trace.STEP))
                        log.trace("The search will continue with literal %s. Branch[%d] becomes 0.", l, d);
                    DEC[d] = l;
                    BRANCH[d] = 0;
                }
                case 4:  // Try l.
                    if (trackChoices) track.add(l);
                    if (tracing.contains(Trace.SEARCH)) {
                        log.trace("Level %d: Trying %s. F=%d/%d", d, l, F, N);
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
                            FORCE.clear();
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
                    if (tracing.contains(Trace.FIXING)) log.trace("fixing %s", L);

                    Variable X = L.var;
                    X.VAL = RT + (L.id & 1);  // TODO magic number
                    // Remove variable X from the free list and from all TIMP pairs (ex. 137).
                    final int N1 = N - G;
                    Variable y = VAR[N1];
                    int j = X.INX;
                    VAR[j] = y;
                    y.INX = j;
                    VAR[N1] = X;
                    X.INX = N1;
                    if (!deactivate(L)) {
                        state = 11;
                        continue STEP;
                    }
                    state = 6;
                    continue;
                }
                /* Steps 8 and 9 are in the method consider(). */
                case 10:  // Accept real truths.
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
                        // reactivate the TIMP pairs that involve X and restore X to the free list (ex. 137)
                        reactivate(R[E]);
                        R[E].var.VAL = 0;
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
                        log.info("UNSAT after %d nodes", nodeCount);
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

    private Optional<boolean[]> solution() {
        boolean sat[] = new boolean[var.length-1];
        for (int i = 1; i < var.length; ++i) sat[i - 1] = (var[i].VAL & 1) == 0;
        return Optional.of(sat);
    }

    /**
     * Knuth's Algorithm X, which is used to gather information guiding the selection of literals
     * in Algorithm L.
     */
    class AlgorithmX {
        private final AlgorithmY Y = new AlgorithmY();
        private final Variable[] CAND;  // candidate variables for algorithm X
        private int nCAND;  // Number of used entries in above array
        private final ArrayList<Literal> CANDL = new ArrayList<>();  // candidate literals
        private final Lookahead[] look;  // lookahead entries
        int S;  // number of valid look[] entries
        int BASE;  // current base truth level (shared between algorithms X and Y

        private final int C0 = 30, C1 = 600;  // See Ex. 148
        private final Heap<Variable> candidateHeap = new Heap<>();
        private final ConnectedComponents connectedComponents = new ConnectedComponents();

        AlgorithmX() {
            CAND = new Variable[nVariables + 1];
            nCAND = 0;
            look = new Lookahead[2*nVariables];
            Arrays.setAll(look, i -> new Lookahead());
        }

        /*
         * Put free variables into the CAND array. If participantsOnly, be sure to only admit variables which
         * are participants.
         */
        private void selectCandidates(boolean participantsOnly) {
            nCAND = 0;
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
                CAND[nCAND++] = v;
            }
        }

        /**
         * Knuth's Algorithm X, which is used to gather information guiding the selection of literals
         * in Algorithm L.
         */
        Result X() {
            if (F == nVariables) {
                log.trace("Returning because F == N before we even start X");
                return Result.SAT;
            }
            final int N = nVariables - F;
            final float[] hd = computeHeuristics();
            // Step X3: Preselect candidates.
            // First select all free participants.

            selectCandidates(SIGL > 0);

            if (nCAND == 0) {
                if (alreadySAT()) return Result.SAT;
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
            for (int i = 0; i < nCAND; ++i) {
                r_sum += CAND[i].rating;
            }

            // While C > 2 C_max, delete all elements of CAND whose rating
            // is less than the mean rating; but terminate the loop if no elements are
            // actually deleted.
            while (nCAND > 2 * C_max) {
                // Compute the mean score.
                double r_mean = r_sum / nCAND;
                r_sum = 0.0;
                int removed = 0;
                for (int i = 0; i < nCAND; ) {
                    final double score = CAND[i].rating;
                    if (score < r_mean) {
                        // This is a bad one. Pull a new one from the end of the candidates list.
                        CAND[i] = CAND[--nCAND];
                        ++removed;
                    } else {
                        // This is a good one. Keep it, accumulate its score, and go to the next.
                        r_sum += score;
                        ++i;
                    }
                }
                if (removed == 0) break;
            }
            // Finally, if C > C_max, reduce C to C_max by retaining only top-ranked
            // candidates.
            if (nCAND > C_max) {
                candidateHeap.heapify(CAND, nCAND);
                while (nCAND-- > C_max) candidateHeap.pop();
            }

            ++BSTAMP;
            // Mark surviving candidates with the new BSTAMP value, and compute big H with equation (67).
            for (int i = 0; i < nCAND; ++i) {
                final Variable c = CAND[i];
                for (int candlit = poslit(c).id; candlit <= neglit(c).id; ++candlit) {
                    final Literal l = lit[candlit];
                    l.bstamp = BSTAMP;
                    l.arcs.clear();
                }
            }
            // Compute candidate BIMP list.
            CANDL.clear();
            for (int i = 0; i < nCAND; ++i) {
                final Variable c = CAND[i];
                for (int candlit = poslit(c).id; candlit <= neglit(c).id; ++candlit) {
                    final Literal u = lit[candlit];
                    CANDL.add(u);
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
                            // log.trace("arc for %d: %s -> %d, %d -> %s", dl(candlit), v, dl(candlit), dl(not(candlit)), v.not);
                            v.arcs.add(u);
                            u.not.arcs.add(v.not);
                        }
                    }
                }
            }

            // One Weird Trick: do we need to reverse the order of the arcs to get our components out in the right
            // order?
            if (knuthCompatible) for (int i = 0; i < CANDL.size(); ++i) Collections.reverse(CANDL.get(i).arcs);

            if (tracing.contains(Trace.FOREST)) {
                for (Literal l : CANDL) {
                    if (!l.arcs.isEmpty()) log.trace("Arcs: %s -> %s", l, l.arcs);
                }
            }

            // X4 [Nest the candidates.]

            connectedComponents.find(CANDL);

            // TODO: Knuth's Tarjan algorithm is modified to notice when ~v lives in v's SCC.
            // Our implementation does not notice this, but it would be easy to check, for
            // all literals among the candidates, that


            // Rip over the components, finding, within each, the literal of maximum rating
            // (this is used as an alternate component representative.) We also check here
            // to see if a component contains a literal contradictory to its CC representative.

            for (int i = 0; i < CANDL.size(); ++i) {
                final Literal l = CANDL.get(i);
                if (l != l.parent && l.var.rating > l.parent.vcomp.var.rating) {
                    l.parent.vcomp = l;
                }
                // TODO: consider doing this in cc.find()
                if (l == l.parent.not) {
                    if (tracing.contains(Trace.LOOKAHEAD)) log.trace("contradiction discovered in lookahead");
                    return Result.UNSAT;
                }
            }

            if (tracing.contains(Trace.FOREST)) {
                log.trace("Strong components:");
                for (Literal s = connectedComponents.settled(); s != null; s = s.link) {
                    final Literal t = s;
                    log.trace(() -> {
                        StringBuilder sb = new StringBuilder(String.format(" %s %.4g", t, t.var.rating));
                        if (t.parent != t) sb.append(" with ").append(t.parent);
                        else if (t.vcomp != t) sb.append(" -> ").append(t.vcomp).append(String.format(" %.4g", t.var.rating));
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
                for (Literal u = connectedComponents.settled(); u != null; u = uu) {
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

            // Construct a sequence of literals LL[j] and corresponding truth offsets LO[j], for 0 <= j < S.
            // This is the "lookahead forest."
            S = 0;
            {
                int j = 0;
                Literal u = root.child, v = null;
                LOOK:
                while (true) {
                    look[S].LL = u.vcomp;
                    u.rank = S++;  // k advances in preorder
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
                            look[i].LO = j;
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
                if (j != S + S) throw new IllegalStateException("confusion(looks)");
            }

            if (tracing.contains(Trace.FOREST)) {
                log.trace("Looks at level %d", d);
                for (int i = 0; i < S; ++i) {
                    log.trace(" %s %d", look[i].LL, look[i].LO);
                }
            }

            // X5 [Prepare to explore.]

            int Up = 0, jp = 0, j = 0;
            // The following seems unnecessary according to experiment
            if (wide) E = F;
            // In the wide case: set fptr = rptr XXX

            BASE = 2;  // Knuth sets BASE = 0 in F6, but sets BASE = 2 in sat11.w
            Literal l = null, l0 = null;
            int xstate = 6;
            // Move to avoid allocation. When to reset this?

            while (true) switch (xstate) {
                case 6: { // [Choose l for lookahead.]
                    l = look[j].LL;
                    T = BASE + look[j].LO;
                    l.H = l.parent != null ? l.parent.H : 0;
                    if (tracing.contains(Trace.LOOKAHEAD))
                        log.trace("looking at %s @%d H=%.4g", l, T, l.H);

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
                    if (j == jp || j == 0 && BASE + 2 * S >= PT) {
                        if (wide) {
                            T = NT;
                            ResetFptr();
                        }
                        return Result.LOOKAHEAD;
                    }
                    xstate = 6;
                    continue;
                case 8: { // [Compute sharper heuristic.]
                    //System.out.printf("now state 8...\n");
                    l0 = l;
                    if (!Perform72(l)) {
                        xstate = 13;
                        continue;
                    }
                    // Then...
                    if (w > 0) {
                        l0.H += w;
                        // log.trace("** now H[%s] = %.4f after adding %.4f parent=%s", l0, l0.H, w, l0.parent);
                        xstate = 10;
                        continue;
                    }
                }
                case 9:  // [Exploit an autarky.]
                    if (l0.H == 0) {
                        if (tracing.contains(Trace.FIXING)) log.trace("autarky at %s\n", l0);
                        if (!X12(l0)) {
                            xstate = 13;
                            continue;
                        }
                    } else {
                        if (tracing.contains(Trace.FIXING)) log.trace(" autarky %s -> %s (%.4f)", l0.parent, l0, l0.H);
                        // Generate the binary clause l0 | ~PARENT(l0)
                        appendToBimp(l0.not, l0.parent.not);
                        appendToBimp(l0.parent, l0);
                        // In sat11.w, ll = l0.parent, looklit = l0, and he writes:
                        //     oo,stamp[thevar(looklit)]=stamp[thevar(ll)]^((looklit^ll)&1);
                        // but this is only done in the 3SAT case, because:
                        //     We aren't allowed to upgrade the stamp value of |looklit| to
                        //     the stamp value of |ll|, because that would violate an important
                        //     invariant relation: Our mechanism for undoing virtual changes to large clauses
                        //     requires that the literals in~|rstack| have monotonically decreasing
                        //     levels of truth.
                        if (!wide) l0.var.VAL = l0.parent.var.VAL ^ ((l0.id^l0.parent.id) & 1);
                        // TODO: consider rewrite above to use functions instead of magic bit operations
                    }
                case 10:  // [Optionally look deeper.]
                    if (useY) {
                        if (!Y.y(j, l0)) {
                            if (tracing.contains(Trace.LOOKAHEAD)) log.trace("y is done, and returned false, so off to step 13");
                            xstate = 13;
                            continue;
                        }
                        if (tracing.contains(Trace.LOOKAHEAD)) log.trace("y is done");
                    }
                case 11:  // [Exploit necessary assignments.]
                    List<Literal> bimp = l0.not.BIMP;
                    // Knuth looks for these in reverse-BIMP order.
                    for (int i = l0.not.BSIZE - 1; i >= 0; --i) {
                        Literal u = bimp.get(i);
                        Fixity f = fixity(u);
                        if (f == Fixity.FIXED_T && u.var.VAL < PT) {
                            if (tracing.contains(Trace.FIXING)) log.trace(" necessary %s", u);
                            X12(u);
                        }
                    }
                    xstate = 7;
                    continue;
                case 13:  // [Recover from conflict.]
                    if (tracing.contains(Trace.LOOKAHEAD)) log.trace("lookahead conflict at %s", l0);
                    if (T < PT) {
                        l = l0.not;
                        if (!X12(l)) {
                            return Result.UNSAT;
                        }
                        xstate = 7;
                        continue;
                    }
                    return Result.UNSAT;  // we have discovered a contradiction
                default:
                    throw new IllegalStateException();
            }
        }


        private boolean X12(Literal l) {
            FORCE.add(l);
            if (tracing.contains(Trace.FIXING)) log.trace("forcing %s (queue now contains %d)", l, FORCE.size());
            int oldT = T;
            T = PT;
            boolean result = Perform72(l);
            T = oldT;
            return result;
        }

        private boolean alreadySAT() {
            // "Terminate happily, however, if all free clauses are satisfied...."
            // From Ex. 152:
            //  "Indeed, the absence of free participants means that the fixed-true
            //   literals form an autarky. If TSIZE(l) is nonzero for any free literal
            //   l, some clause is unsatisfied. Otherwise all clauses are satisfied
            //   unless some free l has an unfixed literal lʹ ∈ BIMP(l)."

            for (int vi = 0; vi < nVariables - F; ++vi) {
                final Variable v = VAR[vi];
                for (int li = poslit(v).id; li <= neglit(v).id; ++li) {
                    final Literal l = lit[li];
                    // l is a free literal since v is a free variable.
                    if (l.TSIZE > 0 || l.not.KSIZE > 0) return false;  // TODO: this is slightly unprincipled
                    List<Literal> bimpl = l.BIMP;
                    for (int j = 0; j < l.BSIZE; ++j) {
                        if (!isfixed(bimpl.get(j))) return false;
                    }
                }
            }
            return true;
        }

        class AlgorithmY {
            private final float β = 0.999f;
            private float τ = 0;
            private final int Y = 10;
            private int jhat, jhatp;  // XXX consider folding Y7 and making these local
            private int DT;

            private boolean y(final int j, final Literal l0) {
                // Y1. [Filter.]
                // XXX in the fascicle, d == 0 is not a condition, but should be according to sat11.w
                if (d == 0 || l0.DFAIL == ISTAMP || T + 2 * S * (Y+1) > PT) return true; /* XXX: we didn't do anything */
                if (l0.H <= τ) {
                    τ *= β;
                    return true; /* XXX is this the right thing to return when we don't do anything */
                }
                // Y2. [Initialize.]
                int LBASE;
                if (false)  {
                    // the knuth fascicle form of the settings.
                    BASE = T-2;
                    LBASE = BASE + 2*S*Y;
                    DT = LBASE + look[j].LO;
                } else {
                    // the sat11.w form of the settings
                    LBASE = T + 2*S*Y;
                    DT = LBASE + T - BASE;
                    BASE = T;
                }
                if (tracing.contains(Trace.LOOKAHEAD)) log.trace("BASE %d LBASE %d DT %d", BASE, LBASE, DT);
                jhat = jhatp = 0;
                // Warning: Knuth has it LBASE+T-BASE.
                // also BASE=CS
                E = F;
                // CONFLICT = Y8
                int oldT = T;
                T = DT;
                if (!propagate(l0)) throw new IllegalStateException("uh oh: initial propagate at level DT led to contra");
                T = oldT; // is this necessary since we're about to enter state 3 XXX
                Literal l = null;
                int ystate = 3;
                // Y3. [Choose l for double look.]
                while (true) switch (ystate) {
                    case 3:  // Y3. [Choose l for double look.]
                        l = look[jhat].LL;  // XXX in Knuth these are j, not jhat
                        T = BASE + look[jhat].LO;  // XXX ditto
                        if (tracing.contains(Trace.LOOKAHEAD)) log.trace("dlooking at %s (%d)", l, T);
                        Fixity fl = fixity(l);
                        if (fl == Fixity.UNFIXED) {
                            ystate = 5;
                            continue;
                        }
                        // If l is fixed but not Dfalse...
                        if (fl == Fixity.FIXED_F && l.var.VAL < DT) Y7(l.not);
                    case 4:  // Y4. [Move to next.]
                        ++jhat;
                        if (jhat == S) {
                            jhat = 0;
                            BASE += 2 * S;
                        }
                        ystate = (jhatp == jhat || jhat == 0 && BASE == LBASE) ? 6 : 3;
                        continue;
                    case 5:  // Y5. [Look ahead.]
                        ystate = !Perform73(l) ? 8 : 4;
                        continue;
                    case 6:  // Y6. [Finish.]
                        while (!W.isEmpty()) {
                            final Literal w = W.pop();
                            if (tracing.contains(Trace.LOOKAHEAD)) log.trace("windfall %s->%s", l, w);
                            boolean oo = newBinaryClause(l0.not, w);
                            if (!oo) throw new IllegalStateException("nbc return false in Y??");
                        }
                        BASE = LBASE;
                        T = DT;
                        τ = l0.H;
                        l0.DFAIL = ISTAMP;
                        if (tracing.contains(Trace.LOOKAHEAD)) log.trace("y came back, now T is %d", T);

                        return true;
                    case 8:  // Y8. [Recover from conflict.]
                        if (T < DT) {
                            if (!Y7(look[jhat].LL.not)) continue;
                            ystate = 4;
                            continue;
                        }
                        BASE = LBASE; /* XXX is this in knuth? it is in sat11.w in "Recover from a double lookahead contradiction" */
                        return false; // exit to step X13
                }
            }
            /** Y7. [Make l0hat false.] */
            private boolean Y7(Literal l) {
                jhatp = jhat;
                int Tp = T;
                T = DT;
                if (!Perform73(l)) return false;
                T = Tp;
                W.push(l);
                return true;
            }
        }
    }

    private String truthName(int t) {
        if (t >= RT) return "real";
        if (t >= NT) return "near";
        if (t >= PT) return "proto";
        return Integer.toString(t);
    }

    private Literal poslit(Variable v) { return lit[poslit(v.id)]; }
    private Literal neglit(Variable v) { return lit[neglit(v.id)]; }
    boolean isfree(Literal l) { return l.var.VAL < RT; }
    boolean isfixed(Literal l) { return l.var.VAL >= T; }
    String track() { return track.toString(); }
}
