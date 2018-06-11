package net.littleredcomputer.knuth7;

import com.google.common.base.Splitter;

import java.io.BufferedReader;
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
}
