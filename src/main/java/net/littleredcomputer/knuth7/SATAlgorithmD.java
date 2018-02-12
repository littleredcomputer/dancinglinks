package net.littleredcomputer.knuth7;

import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import java.util.function.IntUnaryOperator;
import java.util.stream.Collectors;

public class SATAlgorithmD extends AbstractSATSolver {
    SATAlgorithmD(SATProblem problem) {
        super("D", problem);
    }

    @Override
    public Optional<boolean[]> solve() {
        start();
        final int nVariables = problem.nVariables();
        int stepCount = 0;
        int[] m = new int[nVariables + 1];
        int[] x = new int[nVariables + 1];
        int[] H = new int[nVariables + 1];
        int[] NEXT = new int[nVariables + 1];
        int[] W = new int[2 * nVariables + 2];
        int[] L = new int[problem.nLiterals()];
        int[] LINK = new int[problem.nClauses() + 1];
        int[] START = new int[problem.nClauses() + 1];
        int d = 0;
        int h = 0;
        int t = 0;
        int c = 0;
        for (int ciz = problem.nClauses() - 1; ciz >= 0; --ciz) {
            List<Integer> clause = problem.getClause(ciz);
            START[ciz+1] = c;
            LINK[ciz+1] = W[clause.get(0)];
            W[clause.get(0)] = ciz+1;
            for (Integer l : clause) L[c++] = l;
        }
        START[0] = L.length;
        int k;
        for (k = nVariables; k > 0; --k) {
            x[k] = -1;
            if (W[2*k] != 0 || W[2*k+1] != 0) {
                NEXT[k] = h;
                h = k;
                if (t == 0) t = k;
            }
            if (t != 0) NEXT[t] = h;
        }

        IntUnaryOperator isUnit = l -> {
            // For each clause c in the watch list of literal l, consider the
            // sub-list of literals excluding the first. If all of these are
            // false, then we have discovered a unit clause involving l, so we
            // return 1; otherwise 0.
            int j = W[l];
            while (j != 0) {
                boolean unit = true;
                for (int p = START[j] + 1; p != START[j-1]; ++p) {
                    if (x[L[p]>>1] != (L[p] & 1)) {
                        unit = false;
                        break;
                    }
                }
                if (unit) return 1;
                j = LINK[j];
            }
            return 0;
        };

        int state = 2;
        boolean debug = false;
        while(true) {
            ++stepCount;
            if (stepCount % logCheckSteps == 0) maybeReportProgress(stepCount, m);
            // Algorithm D. The case state labels correspond to Knuth's numbering of the steps.
            // Step 1 is already complete, above.
            switch (state) {
                case 2:  // Success?
                    if (debug) {
                        System.out.print("Active Ring: (");
                        if (t == 0) System.out.println(")");
                        else {
                            System.out.printf("%d ", h);
                            int p = NEXT[h];
                            while (p != h) {
                                System.out.printf("%d ", p);
                                p = NEXT[p];
                            }
                            System.out.println(")");
                        }
                        System.out.println("    H: " + Arrays.toString(H));
                        System.out.println("    X: " + Arrays.toString(x));
                        System.out.println("    L: " + Arrays.toString(L));
                        System.out.println("    W: " + Arrays.toString(W));
                        System.out.println(" link: " + Arrays.toString(LINK));
                        System.out.println("start: " + Arrays.toString(START));
                    }


                    if (t == 0) {
                        boolean[] bs = new boolean[nVariables];
                        for (int j = 1; j <= nVariables; ++j) bs[j-1] = x[j] == 1;
                        return Optional.of(bs);
                    }
                    k = t;
                case 3:  // Look for unit clauses.
                    h = NEXT[k];
                    int f = isUnit.applyAsInt(2*h) + 2*isUnit.applyAsInt(2*h+1);
                    if (debug) System.out.printf("isunit %d: %d, %d: %d; so f is %d\n", 2*h, isUnit.applyAsInt(2*h), 2*h+1, isUnit.applyAsInt(2*h+1), f);
                    if (f == 3) {
                        state = 7;
                        continue;
                    } else if (f == 1 || f == 2) {
                        m[d+1] = f+3;
                        t = k;
                        state = 5;
                        continue;
                    } else if (h != t) {
                        k = h;
                        state = 3;
                        continue;
                    }
                /* case 4: */  // Two-way branch.
                    h = NEXT[t];
                    m[d+1] = (W[2*h] == 0 || W[2*h+1] != 0) ? 1 : 0;
                case 5:  // Move on.
                    ++d;
                    H[d] = k = h;
                    if (t == k) {
                        t = 0;
                    } else {
                        NEXT[t] = h = NEXT[k];
                    }
                case 6: {  // Update watches.
                    int b = (m[d] + 1) % 2;
                    x[k] = b;
                    // clear the watch list for -x_k ex. 130
                    int l = 2 * k + b;
                    if (debug) System.out.printf("Chosen: x[%d] = %d, so clear watch list for %d\n", k, b, l);
                    int j = W[l];
                    W[l] = 0;
                    while (j != 0) {
                        int jj = LINK[j];  // (i)
                        int i = START[j];
                        int p = i+1;
                        while (x[L[p]>>1] == (L[p] & 1)) {  // (ii)
                            ++p;
                        }
                        int ll = L[p];  // (iii)
                        L[p] = l;
                        L[i] = ll;
                        p = W[ll];  // (iv)
                        int q = W[ll^1];
                        if (p == 0 && q == 0 && x[ll>>1] < 0) {
                            if (t == 0) {  // (v)
                                t = h = ll>>1;
                                NEXT[t] = h;
                            } else {
                                NEXT[ll>>1] = h;
                                h = ll>>1;
                                NEXT[t] = h;
                            }
                        }
                        LINK[j] = p;  // (vi)
                        W[ll] = j;
                        j = jj;  // (vii)
                    }
                    state = 2;
                    continue;
                }
                case 7:  // Backtrack.
                    if (debug) System.out.println("step 7 (backtrack!)");
                    t = k;
                    while(m[d] >= 2) {
                        k = H[d];
                        x[k] = -1;
                        if (W[2*k] != 0 || W[2*k+1] != 0) {
                            NEXT[k] = h;
                            h = k;
                            NEXT[t] = h;
                        }
                        --d;
                    }
                case 8:  // Failure?
                    if (d > 0) {
                        m[d] = 3 - m[d];
                        k = H[d];
                        state = 6;
                        continue;
                    }
                    return Optional.empty();
            }
        }
    }
}
