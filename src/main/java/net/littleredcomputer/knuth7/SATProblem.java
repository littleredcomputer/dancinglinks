package net.littleredcomputer.knuth7;

import java.io.*;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class SATProblem {
    private static Pattern pLineRe = Pattern.compile("p\\s+cnf\\s+([0-9]+)\\s+([0-9]+)\\s*");
    private final int nVariables; // XXX do we care?
    private final List<int[]> clauses = new ArrayList<>();
    private int nLiterals = 0;

    private SATProblem(int nVariables) {
        if (nVariables < 1) throw new IllegalArgumentException("Must have at least one variable");
        this.nVariables = nVariables;
    }


    private int nClauses() {
        return clauses.size();
    }

    private static StreamTokenizer tokenizer(Reader r) {
        StreamTokenizer t = new StreamTokenizer(r);
        t.resetSyntax();
        t.parseNumbers();
        t.whitespaceChars(0, ' ');
        return t;
    }

    /**
     * Implement the encoding described in 7.2.2.2 (57)
     *
     * @param literal A positive or negative variable number
     * @return The [2n|2n+1]-encoded valude
     */
    private static int encodeLiteral(int literal) {
        return literal > 0 ? 2 * literal : -2 * literal + 1;
    }

    private void addClause(List<Integer> literals) {
        int[] ls = literals.stream().map(SATProblem::encodeLiteral).sorted().mapToInt(i -> i).toArray();
        clauses.add(ls);
        nLiterals += ls.length;
    }

    public Optional<boolean[]> algorithmA() {
        int nCells = 2 + 2 * nVariables + nLiterals;
        int[] L = new int[nCells];
        int[] F = new int[nCells];
        int[] B = new int[nCells];
        int[] C = new int[nCells];
        int[] START = new int[clauses.size() + 1];
        int[] SIZE = new int[clauses.size() + 1];
        int c = 2;
        // For each variable, populate clause index headers (2 for each variable: asserted and denied)
        for (; c < 2 * nVariables + 2; ++c) {
            F[c] = B[c] = c;
        }
        // Process clauses in reverse order, and literals in descending order of variable (because Knuth does).
        // c is the index of the next free slot in the (L, F, B, C) arrays. ciz is the zero-based clause index.
        for (int ciz = clauses.size() - 1; ciz >= 0; --ciz) {
            int[] clause = clauses.get(ciz);
            START[ciz + 1] = c;
            SIZE[ciz + 1] = clause.length;
            for (int k = clause.length - 1; k >= 0; --k) {
                int l = clause[k];
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
        int a = clauses.size();
        int d = 1;
        int l = 0;
        int[] m = new int [nVariables + 1];
        int state = 2;

        LOOP: while (true) {
            // System.out.println("solving. state " + state + " d " + d);
            switch (state) {
                case 2:  // Choose.
                    l = 2 * d;
                    if (C[l] <= C[l + 1]) ++l;
                    m[d] = (l & 1) + (C[l ^ 1] == 0 ? 4 : 0);
                    // System.out.println("move " + Arrays.toString(Arrays.copyOfRange(m, 1, d+1)));
                    // System.out.println("l " + l + " C[l] " + C[l] + " a " + a);
                    if (C[l] == a) {
                        // Success: convert the move notation into a satisfying assignment.
                        boolean[] solution = new boolean[nVariables];
                        for (int i = 1; i <= nVariables; ++i) solution[i-1] = (m[i] & 1) == 0;
                        return Optional.of(solution);
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

    public static SATProblem parseFrom(Reader r) {
        BufferedReader br = new BufferedReader(r);
        int nVar;
        int nClause;
        SATProblem sat;
        try {
            while (true) {
                String line = br.readLine();
                if (line.startsWith("c")) continue;
                if (line.startsWith("p")) {
                    Matcher m = pLineRe.matcher(line);
                    if (!m.matches()) throw new IllegalArgumentException("invalid p line");
                    nVar = Integer.parseInt(m.group(1));
                    nClause = Integer.parseInt(m.group(2));
                    break;
                }
                throw new IllegalArgumentException("Invalid dimacs preamble");
            }
            sat = new SATProblem(nVar);
            StreamTokenizer tk = tokenizer(br);
            int token;
            List<Integer> literals = new ArrayList<>();
            while ((token = tk.nextToken()) != StreamTokenizer.TT_EOF) {
                if (token != StreamTokenizer.TT_NUMBER) throw new IllegalArgumentException("Illegal literal: " + token);
                int l = (int) tk.nval;
                if (l > nVar || l < -nVar)
                    throw new IllegalArgumentException("Literal out of bounds established by p cnf: " + l);
                if (l == 0) {
                    if (literals.isEmpty())
                        throw new IllegalArgumentException("Empty clause (therefore problem is trivially unsatisfiable): " + tk + "," + tk.nval + "," + tk.sval);
                    if (sat.nClauses() >= nClause)
                        throw new IllegalArgumentException("More clauses specified than allowed for in p statement");
                    sat.addClause(literals);
                    literals.clear();
                    continue;
                }
                literals.add(l);
            }
            if (!literals.isEmpty()) throw new IllegalArgumentException("dangling final clause lacks zero-termination");
        } catch (IOException e) {
            throw new IllegalArgumentException("Parse error", e);
        }
        return sat;
    }
}
