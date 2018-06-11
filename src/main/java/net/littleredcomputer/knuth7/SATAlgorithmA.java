package net.littleredcomputer.knuth7;

import com.google.common.collect.Lists;

import java.util.Collections;
import java.util.List;
import java.util.Optional;

public class SATAlgorithmA extends AbstractSATSolver {

    SATAlgorithmA(SATProblem p) {
        super("A", p);
    }

    @Override
    public Optional<boolean[]> solve() {
        start();
        final List<List<Integer>> clauses = problem.encodedClauses();
        final int nVariables = problem.nVariables();
        final int nClauses = clauses.size();
        int nCells = 2 + 2 * nVariables + problem.nLiterals();
        int[] L = new int[nCells];
        int[] F = new int[nCells];
        int[] B = new int[nCells];
        int[] C = new int[nCells];
        int[] START = new int[nClauses + 1];
        int[] SIZE = new int[nClauses + 1];
        int c = 2;
        // For each variable, populate clause index headers (2 for each variable: asserted and denied)
        for (; c < 2 * nVariables + 2; ++c) {
            F[c] = B[c] = c;
        }
        // Process clauses in reverse order, and literals in descending order of variable (because Knuth does).
        // c is the index of the next free slot in the (L, F, B, C) arrays. ciz is the zero-based clause index.
        for (int ciz = nClauses - 1; ciz >= 0; --ciz) {
            List<Integer> clause = Lists.newArrayList(clauses.get(ciz));
            Collections.sort(clause);
            START[ciz + 1] = c;
            SIZE[ciz + 1] = clause.size();
            for (int k = clause.size() - 1; k >= 0; --k) {
                int l = clause.get(k);
                L[c] = l;
                C[c] = ciz + 1;
                ++C[l];
                int f = F[l];
                F[l] = c;
                F[c] = f;
                B[c] = l;
                B[f] = c;
                ++c;
            }
        }

//        IntFunction<String> π = i -> String.format("%4d", i);
//        System.out.println("  " + IntStream.range(0, nCells).mapToObj(π).collect(Collectors.joining()));
//        System.out.println("L:" + Arrays.stream(L).mapToObj(π).collect(Collectors.joining()));
//        System.out.println("F:" + Arrays.stream(F).mapToObj(π).collect(Collectors.joining()));
//        System.out.println("B:" + Arrays.stream(B).mapToObj(π).collect(Collectors.joining()));
//        System.out.println("C:" + Arrays.stream(C).mapToObj(π).collect(Collectors.joining()));
//        System.out.println("S:" + Arrays.stream(START).mapToObj(π).collect(Collectors.joining()));
//        System.out.println("z:" + Arrays.stream(SIZE).mapToObj(π).collect(Collectors.joining()));

        // A1.
        int a = nClauses;
        int d = 1;
        int l = 0;
        int[] m = new int [nVariables + 1];
        int state = 2;

        LOOP: while (true) {
            // System.out.println("solving. state " + state + " d " + d);
            ++stepCount;
            if (stepCount % logCheckSteps == 0) maybeReportProgress(m);
            switch (state) {
                case 2:  // Choose.
                    l = 2 * d;
                    if (C[l] <= C[l + 1]) ++l;
                    m[d] = (l & 1) + (C[l ^ 1] == 0 ? 4 : 0);
                    // System.out.println("move " + Arrays.toString(Arrays.copyOfRange(m, 1, d+1)));
                    // System.out.println("l " + l + " C[l] " + C[l] + " a " + a);
                    if (C[l] == a) {
                        return problem.solutionFromSteps(m);
                    }
                case 3: {  // Remove -l.
                    int p = F[l ^ 1];
                    while (p >= 2 * nVariables + 2) {
                        int j = C[p];
                        int i = SIZE[j];
                        assert i > 0;
                        if (i == 1) {
                            // "interrupt that loop..."
                            p = B[p];
                            while (p >= 2 * nVariables + 2) {
                                j = C[p];
                                i = SIZE[j];
                                SIZE[j] = i + 1;
                                p = B[p];
                            }
                            state = 5;
                            continue LOOP;
                        }
                        SIZE[j] = i - 1;
                        p = F[p];
                    }
                }
                /* case 4: */ {  // Deactivate l's clauses.
                    int p = F[l];
                    while (p >= 2 * nVariables + 2) {
                        int j = C[p];
                        int i = START[j];
                        p = F[p];
                        for (int s = i; s < i + SIZE[j] - 1; ++s) {
                            int q = F[s];
                            int r = B[s];
                            B[q] = r;
                            F[r] = q;
                            --C[L[s]];
                        }
                    }
                    a -= C[l];
                    ++d;
                    state = 2;
                    continue;
                }
                case 5:  // Try again.
                    if (m[d] < 2) {
                        m[d] = 3 - m[d];
                        l = 2 * d + (m[d] & 1);
                        state = 3;
                        continue;
                    }
                case 6:  // Backtrack.
                    if (d == 1) return Optional.empty();  // unsatisfiable
                    --d;
                    l = 2 * d + (m[d] & 1);
                case 7: {  // Reactivate l's clauses
                    a += C[l];
                    for (int p = B[l]; p >= 2 * nVariables + 2;) {
                        int j = C[p];
                        int i = START[j];
                        p = B[p];
                        for (int s = i; s < i + SIZE[j] - 1; ++s) {
                            int q = F[s];
                            int r = B[s];
                            B[q] = F[r] = s;
                            ++C[L[s]];
                        }
                    }
                }
                case 8: {  // Unremove -l.
                    for (int p = F[l^1]; p >= 2 * nVariables + 2;) {
                        int j = C[p];
                        int i = SIZE[j];
                        SIZE[j] = i + 1;
                        p = F[p];
                    }
                    state = 5;
                }
            }
        }
    }
}
