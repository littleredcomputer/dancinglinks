package net.littleredcomputer.knuth7;

import com.google.common.collect.ImmutableList;

import java.io.*;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class SATProblem {
    private static Pattern pLineRe = Pattern.compile("p\\s+cnf\\s+([0-9]+)\\s+([0-9]+)\\s*");
    private final int nVariables; // XXX do we care?
    private final List<ImmutableList<Integer>> clauses = new ArrayList<>();
    private int nLiterals = 0;
    private int height = 0;

    private SATProblem(int nVariables) {
        if (nVariables < 1) throw new IllegalArgumentException("Must have at least one variable");
        this.nVariables = nVariables;
    }

    public int nClauses() { return clauses.size(); }
    public int nVariables() { return nVariables; }
    public int nLiterals() { return nLiterals; }
    public int height() { return height; }
    ImmutableList<Integer> getClause(int i) { return clauses.get(i); }

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
     * @param variable A positive or negative variable number
     * @return The [2n|2n+1]-encoded valude
     */
    private static int encodeLiteral(int variable) {
        return variable > 0 ? 2 * variable : -2 * variable + 1;
    }
    static int decodeLiteral(int literal) {
        int sign = ((literal & 1) == 0) ? 1 : -1;
        return sign * (literal >> 1);
    }

    private void addClause(List<Integer> literals) {
        ImmutableList<Integer> ls = literals.stream().map(SATProblem::encodeLiteral).collect(ImmutableList.toImmutableList());
        clauses.add(ls);
        nLiterals += ls.size();
        if (ls.size() > height) height = ls.size();
    }

    private void addEncodedClause(ImmutableList<Integer> encodedLiterals) {
        clauses.add(encodedLiterals);
        nLiterals += encodedLiterals.size();
        if (encodedLiterals.size() > height) height = encodedLiterals.size();
    }

    Optional<boolean[]> solutionFromSteps(int[] steps) {
        // Success: convert the move notation into a satisfying assignment.
        boolean[] solution = new boolean[nVariables];
        for (int i = 1; i < steps.length; ++i) solution[i-1] = (steps[i] & 1) == 0;
        return Optional.of(solution);
    }

    public boolean evaluate(boolean[] solution) {
        CLAUSE: for (int i = 1; i < clauses.size(); ++i) {
            List<Integer> clause = clauses.get(i);
            for (int literal : clause) {
                // One true literal in the clause is enough to make the whole clause true.
                if (solution[(literal>>1) - 1] == ((literal & 1) == 0)) continue CLAUSE;
            }
            return false;  // Any false clause is enough to spoil satisfaction.
        }
        return true;  // No clause was falsified by any literal.
    }

    public static SATProblem parseFrom(String s) {
        return parseFrom(new StringReader(s));
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

    public SATProblem to3SAT() {
        if (this.height <= 3) return this;
        List<ImmutableList<Integer>> newClauses = new ArrayList<>();
        int nextVariable = nVariables + 1;
        for (ImmutableList<Integer> c : clauses) {
            if (c.size() <= 3) {
                newClauses.add(c);
            } else {
                // ImmutableList.Builder<Integer> b = new ImmutableList.Builder<>();
                // Add the leftmost part
                final int N = c.size();
                newClauses.add(ImmutableList.of(c.get(0), c.get(1), encodeLiteral(nextVariable)));
                // Add the middle parts
                for (int j = 2; j < N - 2; ++j, ++nextVariable) {
                    newClauses.add(ImmutableList.of(c.get(j), encodeLiteral(-nextVariable), encodeLiteral(nextVariable+1)));
                }
                // Add the last clause
                newClauses.add(ImmutableList.of(encodeLiteral(-nextVariable), c.get(N - 2), c.get(N - 1)));
                ++nextVariable;
            }
        }
        SATProblem q = new SATProblem(nextVariable-1);
        newClauses.forEach(q::addEncodedClause);
        return q;
    }
}
