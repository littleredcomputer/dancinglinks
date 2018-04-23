package net.littleredcomputer.knuth7;

import com.google.common.primitives.Booleans;

import java.io.InputStreamReader;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import static com.github.npathai.hamcrestopt.OptionalMatchers.isEmpty;
import static com.github.npathai.hamcrestopt.OptionalMatchers.isPresentAndIs;
import static java.util.stream.Collectors.toList;
import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertThat;

class TestProblems {
    /**
     * Generate the SAT problem waerden(j, j; n), defined by 7.2.2.2 (10), in dimacs format.
     *
     * @param j Number of consecutive 0s to require
     * @param k Number of consecutive 1s to require
     * @param n Length of binary string
     * @return the problem posed in dimacs CNF format
     */
    SATProblem waerdenProblem(int j, int k, int n) {
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

    /**
     * Write the clauses corresponding to S1(y_i...) where the y_i correspond
     * to the positions of the true bits (counting from 1).
     *
     * @param sb clauses written to this string.
     */
    private int S1(List<Boolean> bits, StringBuilder sb) {
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

    int waerden(int j, int k, Function<SATProblem, AbstractSATSolver> solver) {
        // waerdenProblem(j, k, n) is satisfiable iff n < W(j, k). Compute W by finding the smallest
        // integer for which the associated problem is unsatisfiable.
        return IntStream.range(1, 1000)
                .filter(i -> !solver.apply(waerdenProblem(j, k, i)).solve().isPresent())
                .findFirst()
                .orElseThrow(() -> new IllegalStateException("did not establish Waerden value"));
    }

    SATProblem langfordProblem(int n) {
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

    public void testLangfordWith(Function<SATProblem, AbstractSATSolver> a) {
        Supplier<IntStream> range = () -> IntStream.range(2, 10);
        // The langford problem is solvable iff i mod 4 in {0, 3}. When it is solvable, we should expect the
        // number of true variables to be equal to the problem size (i.e., each digit receives exactly one
        // (dual) placement). When i mod 4 in {1, 2}, the solver should refute the problem instance.
        List<Optional<Integer>> expected = range.get().mapToObj(i -> i % 4 == 0 || i % 4 == 3 ? Optional.of(i) : Optional.<Integer>empty()).collect(toList());
        Stream<Optional<Integer>> observed = range.get().mapToObj(i -> {
            SATProblem Li = langfordProblem(i);
            return a.apply(Li).solve()
                    .map(k -> Arrays.copyOfRange(k, 0, Li.nVariables()))
                    .map(Booleans::asList)
                    .map(bs -> bs.stream().mapToInt(b -> b ? 1 : 0).sum());
        });
        assertThat(observed.collect(toList()), is(expected));
    }


    private static SATProblem fromResource(String name) {
        return SATProblem.parseFrom(new InputStreamReader(TestProblems.class.getClassLoader().getResourceAsStream(name)));
    }

    private static SATProblem knuthFromResource(String name) {
        return SATProblem.parseKnuth(new InputStreamReader(TestProblems.class.getClassLoader().getResourceAsStream(name)));
    }

    private static final SATProblem hole6 = fromResource("hole6.cnf");
    private static final SATProblem zebra = fromResource("zebra.cnf");
    private static final SATProblem quinn = fromResource("quinn.cnf");
    private static final SATProblem dubois = fromResource("dubois20.cnf");
    private static final SATProblem queen5 = knuthFromResource("queen-5x5-5.sat");
    private static final SATProblem mutex4bitsL1 = knuthFromResource("mutex-fourbits-lemmas-1.sat");
    private static final SATProblem rand3_1061 = knuthFromResource("rand-3-1061-250-314159.sat");
    private static final SATProblem rand3_1062 = knuthFromResource("rand-3-1062-250-314159.sat");
    private static final SATProblem ex6 = SATProblem.parseFrom("p cnf 4 8\n1 2 -3 0 2 3 -4 0 3 4 1 0 4 -1 2 0 -1 -2 3 0 -2 -3 4 0 -3 -4 -1 0 -4 1 -2 0");
    private static final SATProblem ex7 = SATProblem.parseFrom("p cnf 4 7\n1 2 -3 0 2 3 -4 0 3 4 1 0 4 -1 2 0 -1 -2 3 0 -2 -3 4 0 -3 -4 -1 0");
    private static final SATProblem ex152 = SATProblem.parseFrom("p cnf 5 6\n1 2 -3 0 1 -2 3 0 -1 2 -3 0 -1 -2 3 0 2 4 5 0 3 -4 -5 0");
    static final SATProblem rand3_420_100_0 = SATProblem.randomInstance(3, 420, 100, 0);


    void assertSAT(SATProblem p, Function<SATProblem, AbstractSATSolver> a) {
        assertThat(a.apply(p).solve().map(p::evaluate), isPresentAndIs(true));
    }

    void assertUNSAT(SATProblem p, Function<SATProblem, AbstractSATSolver> a) {
        assertThat(a.apply(p).solve(), isEmpty());
    }
    void testHole6With(Function<SATProblem, AbstractSATSolver> a) { assertUNSAT(hole6, a); }
    void testDuboisWith(Function<SATProblem, AbstractSATSolver> a) { assertUNSAT(dubois, a); }
    void testQueen5With(Function<SATProblem, AbstractSATSolver> a) { assertSAT(queen5, a); }
    void testMutex4BitsL1With(Function<SATProblem, AbstractSATSolver> a) { assertUNSAT(mutex4bitsL1, a); }
    void testZebraWith(Function<SATProblem, AbstractSATSolver> a) { assertSAT(zebra, a); }
    void testQuinnWith(Function<SATProblem, AbstractSATSolver> a) { assertSAT(quinn, a); }
    void testEx6With(Function<SATProblem, AbstractSATSolver> a) { assertUNSAT(ex6, a); }
    void testEx7With(Function<SATProblem, AbstractSATSolver> a) { assertSAT(ex7, a); }
}
