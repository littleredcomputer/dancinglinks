package net.littleredcomputer.knuth7;

import com.google.common.base.Splitter;

import java.io.BufferedReader;
import java.io.PrintStream;
import java.io.Reader;
import java.io.StringReader;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import static java.util.stream.Collectors.toList;

public class SATProblem {
    private final static Pattern pLineRe = Pattern.compile("p\\s+cnf\\s+([0-9]+)\\s+([0-9]+)\\s*");
    private final static Splitter splitter = Splitter.on(' ').trimResults().omitEmptyStrings();
    private final int nVariables;
    private final List<List<Integer>> clauses = new ArrayList<>();
    private int nLiterals = 0;
    private int height = 0;

    // TODO: make private when we switch to the builder pattern.
    // The builder pattern ought also to allow named variables.
    SATProblem(int nVariables) {
        if (nVariables < 1) throw new IllegalArgumentException("Must have at least one variable");
        this.nVariables = nVariables;
    }

    int nClauses() {
        return clauses.size();
    }
    List<List<Integer>> encodedClauses() { return Collections.unmodifiableList(clauses); }

    public int nVariables() {
        return nVariables;
    }
    public int nLiterals() {
        return nLiterals;
    }

    int height() {
        return height;
    }

    List<Integer> getClause(int i) {
        return clauses.get(i).stream().map(SATProblem::decodeLiteral).collect(toList());
    }

    /**
     * Implement the encoding described in 7.2.2.2 (57)
     *
     * @param variable A positive or negative variable number
     * @return The [2n|2n+1]-encoded value
     */
    private static int encodeLiteral(int variable) {
        return variable > 0 ? 2 * variable : -2 * variable + 1;
    }

    static int decodeLiteral(int literal) {
        int sign = ((literal & 1) == 0) ? 1 : -1;
        return sign * (literal >> 1);
    }

    // TODO: creating a builder class would go a long way toward cleaning up the creation logic.

    void addClause(Iterable<Integer> literals) {
        List<Integer> clause = StreamSupport.stream(literals.spliterator(), false).map(SATProblem::encodeLiteral).collect(Collectors.collectingAndThen(toList(), Collections::unmodifiableList));
        final int s = clause.size();
        nLiterals += s;
        clauses.add(clause);
        if (s > height) height = s;
    }

    private void addEncodedClause(List<Integer> encodedLiterals) {
        clauses.add(encodedLiterals);
        nLiterals += encodedLiterals.size();
        if (encodedLiterals.size() > height) height = encodedLiterals.size();
    }

    Optional<boolean[]> solutionFromSteps(int[] steps) {
        // Success: convert the move notation into a satisfying assignment.
        boolean[] solution = new boolean[nVariables];
        for (int i = 1; i < steps.length; ++i) solution[i - 1] = (steps[i] & 1) == 0;
        return Optional.of(solution);
    }

    /**
     * Evaluate the boolean function represented by the problem's clauses at the specified point
     * @param p (point (i.e., vector of booleans) at which to evaluate
     * @return the truth value of this problem at p
     */
    public boolean evaluate(boolean[] p) {
        CLAUSE:
        for (int i = 1; i < clauses.size(); ++i) {
            List<Integer> clause = clauses.get(i);
            for (int literal : clause) {
                // One true literal in the clause is enough to make the whole clause true.
                if (p[(literal >> 1) - 1] == ((literal & 1) == 0)) continue CLAUSE;
            }
            return false;  // Any false clause is enough to spoil satisfaction.
        }
        return true;  // No clause was falsified by any literal.
    }

    public static SATProblem parseFrom(String s) {
        return parseFrom(new StringReader(s));
    }

    public static SATProblem parseFrom(Reader r) {
        List<Integer> literals = new ArrayList<>();
        Iterator<String> ls = new BufferedReader(r).lines().filter(s -> !s.startsWith("c")).iterator();
        if (!ls.hasNext()) throw new IllegalArgumentException("Missing SAT instance data");
        Matcher m = pLineRe.matcher(ls.next());
        if (!m.matches()) throw new IllegalArgumentException("invalid p line");
        int nVar = Integer.parseInt(m.group(1));
        int nClause = Integer.parseInt(m.group(2));
        SATProblem p = new SATProblem(nVar);
        ls.forEachRemaining(line -> StreamSupport.stream(splitter.split(line).spliterator(), false)
                .mapToInt(Integer::parseInt)
                .forEach(l -> {
                    if (l == 0) {
                        if (literals.isEmpty())
                            throw new IllegalArgumentException("Empty clause, so problem is trivially unsatisfiable");
                        p.addClause(literals);
                        literals.clear();
                    } else {
                        if (l > nVar || l < -nVar) throw new IllegalArgumentException("literal out of declared bounds");
                        literals.add(l);
                    }
                }));
        if (!literals.isEmpty()) throw new IllegalArgumentException("Unterminated final clause");
        if (p.nClauses() != nClause) {
            throw new IllegalArgumentException("Observed clause count disagrees with DIMACS p header");
        }
        return p;
    }

    public static SATProblem parseKnuth(String s) { return parseKnuth(new StringReader(s)); }
    public static SATProblem parseKnuth(Reader r) {
        HashMap<String, Integer> varMap = new HashMap<>();
        List<List<Integer>> clauses = new ArrayList<>();
        new BufferedReader(r).lines()
                .filter(s -> !s.startsWith("~ "))
                .forEach(line -> {
                    List<Integer> clause = new ArrayList<>();
                    for (String lit : splitter.split(line)) {
                        boolean negated = false;
                        if (lit.startsWith("~")) {
                            negated = true;
                            lit = lit.substring(1);
                        }
                        if (!varMap.containsKey(lit)) {
                            varMap.put(lit, varMap.size() + 1);
                        }
                        clause.add(varMap.get(lit) * (negated ? -1 : 1));
                    }
                    clauses.add(clause);
                });
        SATProblem p = new SATProblem(varMap.size());
        clauses.forEach(p::addClause);
        return p;
    }

    /**
     * If this problem contains clauses with length > 3, we construct a new, equivalent
     * 3-SAT instance by replacing the long clauses with new 3-clauses, using new auxiliary
     * variables. Any new variables created will be assigned numbers just beyond those
     * in the original problem. If the original problem is already 3-SAT, we merely return
     * the original instance, no copy is made.
     * @return An equivalent problem in 3-SAT.
     */
    public SATProblem to3SAT() {
        if (this.height <= 3) return this;
        List<List<Integer>> newClauses = new ArrayList<>();
        int nextVariable = nVariables + 1;
        for (List<Integer> c : clauses) {
            if (c.size() <= 3) {
                newClauses.add(c);
            } else {
                // Add the leftmost part
                final int N = c.size();
                newClauses.add(Collections.unmodifiableList(Arrays.asList(c.get(0), c.get(1), encodeLiteral(nextVariable))));
                // Add the middle parts
                for (int j = 2; j < N - 2; ++j, ++nextVariable) {
                    newClauses.add(Collections.unmodifiableList(Arrays.asList(c.get(j), encodeLiteral(-nextVariable), encodeLiteral(nextVariable + 1))));
                }
                // Add the last clause
                newClauses.add(Collections.unmodifiableList(Arrays.asList(encodeLiteral(-nextVariable), c.get(N - 2), c.get(N - 1))));
                ++nextVariable;
            }
        }
        SATProblem q = new SATProblem(nextVariable - 1);
        newClauses.forEach(q::addEncodedClause);
        return q;
    }

    /**
     * Generate a random instance of SAT in precisely the way Knuth does in Fascicle 6.
     * This fidelity is achieved by using the same random number generator and the clause
     * generation technique found in sat-rand-rep.w.
     * <p>
     * A wrinkle: Knuth's generator uses the variables [0,n) and writes to a file. When
     * read, Knuth's input code would then choose 1-based variables. To avoid the intermediate
     * representation, we just use 1-based variables to start with. While all our variables
     * are "off by one" when compared to Knuth's, the problems they represent are equivalent.
     *
     * @param k    size of each clause
     * @param m    number of clauses
     * @param n    number of variables
     * @param seed for random number generator
     * @return random SAT instance
     */
    public static SATProblem randomInstance(int k, int m, int n, int seed) {
        if (k <= 0) throw new IllegalArgumentException("k must be positive!");
        if (m <= 0) throw new IllegalArgumentException("m must be positive!");
        if (n <= 0 || n > 100000000) throw new IllegalArgumentException("n must be between 1 and 99999999");
        if (k > n) throw new IllegalArgumentException("k mustn't exceed n!");
        final SGBRandom R = new SGBRandom(seed);
        SATProblem p = new SATProblem(n);
        int i, ii, t;
        for (int j = 0; j < m; j++) {
            // Generate the jth clause.
            List<Integer> encodedClause = new ArrayList<>(k);
            for (int kk = k, nn = n; kk != 0; kk--, nn = ii) {
                // Set ii to the largest in a random kk out of nn
                for (ii = i = 0; i < kk; i++) {
                    t = i + R.unifRand(nn - i);
                    if (t > ii) ii = t;
                }
                // Bump ii before encoding (see above)
                encodedClause.add(2 * (ii + 1) + (R.nextRand() & 1));
            }
            p.addEncodedClause(Collections.unmodifiableList(encodedClause));
        }
        return p;
    }

    // TODO: redo these to avoid the text format.

    /**
     * Write the clauses corresponding to S1(y_i...) where the y_i correspond
     * to the positions of the true bits (counting from 1).
     *
     * @param sb clauses written to this string.
     */
    private static int S1(List<Boolean> bits, StringBuilder sb) {
        int n = 0;
        // See eq. 7.2.2.2 (13). Step 1: write the clause requiring one bit:
        for (int i = 0; i < bits.size(); ++i) {
            if (bits.get(i)) sb.append(i + 1).append(' ');
        }
        sb.append("0\n");
        ++n;
        // Step 2: write clauses forbidding more than one.
        for (int i = 0; i < bits.size(); ++i) {
            if (bits.get(i)) {
                for (int j = i + 1; j < bits.size(); ++j) {
                    if (bits.get(j)) {
                        sb.append(-i - 1).append(' ').append(-j - 1).append(" 0\n");
                        ++n;
                    }
                }
            }
        }
        return n;
    }


    /**
     * Generate the SAT problem waerden(j, k; n), defined by 7.2.2.2 (10)
     *
     * @param j Number of consecutive 0s to require
     * @param k Number of consecutive 1s to require
     * @param n Length of binary string
     * @return the problem posed in dimacs CNF format
     */
    public static SATProblem waerden(int j, int k, int n) {
        StringBuilder clauses = new StringBuilder();
        int clauseCount = 0;
        // Variables [1,n].
        // No j equally-spaced 0's in a string of length n
        boolean addedSome = true;
        for (int d = 1; addedSome; ++d) {
            addedSome = false;
            for (int i = 1; i + (j - 1) * d <= n; ++i) {
                for (int h = 0; h < j; ++h) {
                    clauses.append(i + d * h).append(' ');
                    addedSome = true;
                }
                clauses.append("0\n");
                ++clauseCount;
            }
        }
        addedSome = true;
        for (int d = 1; addedSome; ++d) {
            addedSome = false;
            for (int i = 1; i + (k - 1) * d <= n; ++i) {
                for (int h = 0; h < k; ++h) {
                    clauses.append(-i - d * h).append(' ');
                    addedSome = true;
                }
                clauses.append("0 \n");
                ++clauseCount;
            }
        }
        return SATProblem.parseFrom(new StringReader("c waerden(" + j + ", " + k + ", " + n + ")\np cnf " + n + ' ' + clauseCount + '\n' + clauses));
    }

    public static SATProblem langford(int n) {
        // We arrange the problem using "vertical" arrays, one for each column of the
        // exact cover problem visualized as a matrix of rows of options. The first n
        // columns (or items) represent the digits; the next 2n columns represent the
        // placement of that digit (two of these per row). See 7.2.2.2 (11) of [F6].
        int row = 0;
        List<List<Boolean>> columns = new ArrayList<>(n + 2 * n);
        for (int i = 0; i < 3 * n; ++i) columns.add(new ArrayList<>());
        for (int i = 0; i < n; ++i) {
            for (int j = 0; j + i + 2 < 2 * n; ++j) {
                for (List<Boolean> c : columns) c.add(false);
                columns.get(i).set(row, true);
                columns.get(n + j).set(row, true);
                columns.get(n + j + i + 2).set(row, true);
                //System.out.printf("row %d means set %d in columns %d and %d\n", row+1, i, j, j+i+2);
                ++row;
            }
        }
        int nClauses = 0;
        StringBuilder sb = new StringBuilder();
        for (List<Boolean> c : columns) nClauses += S1(c, sb);
        return SATProblem.parseFrom(new StringReader("c langford(" + n + ")\np cnf " + row + ' ' + nClauses + "\n" + sb));
    }

    public void printKnuth(PrintStream p, String title) {
        p.println("~ " + title);
        for (int i = 0; i < nClauses(); ++i) {
            List<Integer> c = getClause(i);
            for (int l : c) {
                p.printf("%s%d ", l < 0 ? "~": "", Math.abs(l));
            }
            p.println();
        }
    }
}
