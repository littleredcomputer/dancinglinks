package net.littleredcomputer.knuth7;

import java.util.List;
import java.util.Optional;

public class SATAlgorithmB {
    private final SATProblem problem;
    SATAlgorithmB(SATProblem p) {
        this.problem = p;
    }

    public Optional<boolean[]> solve() {
        final int nVariables = problem.nVariables();
        final int nClauses = problem.nClauses();

        int[] m = new int[nVariables + 1];
        int[] START = new int[nClauses + 1];
        int[] L = new int[problem.nLiterals()];
        int[] W = new int[2 * nVariables + 2];  // one for each literal and its negation, one-based
        int[] LINK = new int[nClauses + 1];

        int c = 0;
        for (int ciz = nClauses - 1; ciz >= 0; --ciz) {
            List<Integer> clause = problem.getClause(ciz);
            START[ciz+1] = c;
            LINK[ciz+1] = W[clause.get(0)];
            W[clause.get(0)] = ciz+1;
            for (Integer l : clause) L[c++] = l;
        }
        START[0] = L.length;

//        IntFunction<String> ø = i -> String.format("%4d", i);
//        BiConsumer<String, int[]> π = (String s, int[] v) -> System.out.println(s + Arrays.stream(v).mapToObj(ø).collect(Collectors.joining()));
//        System.out.println("  " + IntStream.range(0, nLiterals).mapToObj(ø).collect(Collectors.joining()));
//        π.accept("L:", L);
//        π.accept("L:", L);
//        π.accept("S:", START);
//        π.accept("W:", W);
//        π.accept("k:", LINK);

        int d = 1;
        int l = 0;  // XXX
        int state = 2;

        STEP: while (true) {
            switch (state) {
                case 2:  // Rejoice or choose.
                    if (d > nVariables) return problem.solutionFromSteps(m);
                    m[d] = (W[2*d] == 0 || W[2*d+1] != 0) ? 1 : 0;
                    // System.out.println("move " + Arrays.toString(Arrays.copyOfRange(m, 1, d+1)));
                    l = 2*d + m[d];
                case 3: {  // Remove -l if possible
                    for (int j = W[l^1]; j != 0; ) {
                        int i = START[j];
                        int ii = START[j-1];
                        int jj = LINK[j];
                        int k;
                        for (k = i+1; k < ii; ++k) {
                            int ll = L[k];
                            if ((ll >> 1) > d || (ll + m[ll >> 1]) % 2 == 0) {
                                L[i] = ll;
                                L[k] = l^1;
                                LINK[j] = W[ll];
                                W[ll] = j;
                                j = jj;
                                break;

                            }
                        }
                        if (k == ii) {
                            W[l^1] = j;
                            state = 5;
                            continue STEP;
                        }
                    }
                }
                /* case 4: */  // Advance.
                W[l^1] = 0;
                ++d;
                state = 2;
                continue;
                case 5:  // Try again.
                    if (m[d] < 2) {
                        m[d] = 3 - m[d];
                        l = 2*d + (m[d] & 1);
                        state = 3;
                        continue;
                    }
                case 6:  // Backtrack.
                    if (d == 1) return Optional.empty();
                    --d;
                    state = 5;
            }
        }
    }


}
