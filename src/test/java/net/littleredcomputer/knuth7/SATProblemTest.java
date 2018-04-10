package net.littleredcomputer.knuth7;

import com.google.common.collect.ImmutableList;
import org.junit.Test;

import java.io.InputStreamReader;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import static com.github.npathai.hamcrestopt.OptionalMatchers.*;
import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.number.OrderingComparison.greaterThan;
import static org.junit.Assert.assertThat;

public class SATProblemTest {

    @Test
    public void simple() {
        SATProblem.parseFrom(new StringReader("c simple test\nc heh\np cnf 3 2\n1 -3 0\n2 3 -1 0"));
    }

    @Test(expected = IllegalArgumentException.class)
    public void emptyClauseThrows() {
        SATProblem.parseFrom(new StringReader("c empty clause\np cnf 3 3\n1 2 3 0 0 1 2 0"));
    }

    @Test(expected = IllegalArgumentException.class)
    public void literalOutOfBounds() {
        SATProblem.parseFrom(new StringReader("c oob literal\np cnf 3 2\n1 2 3 0\n2 3 4 0"));
    }

    @Test(expected = IllegalArgumentException.class)
    public void tooManyClauses() {
        SATProblem.parseFrom(new StringReader("c oob clause\np cnf 3 2\n1 2 3 0\n2 3 -1 0\n-2 -3 0"));
    }

    @Test(expected = IllegalArgumentException.class)
    public void danglingClause() {
        SATProblem.parseFrom(new StringReader("c unclosed clause\np cnf 3 2\n1 2 3 0\n2 3 -1 0\n-2 -3"));
    }

    private static SATProblem ex6 = SATProblem.parseFrom("p cnf 4 8\n1 2 -3 0 2 3 -4 0 3 4 1 0 4 -1 2 0 -1 -2 3 0 -2 -3 4 0 -3 -4 -1 0 -4 1 -2 0");
    private static SATProblem ex7 = SATProblem.parseFrom("p cnf 4 7\n1 2 -3 0 2 3 -4 0 3 4 1 0 4 -1 2 0 -1 -2 3 0 -2 -3 4 0 -3 -4 -1 0");
    private static SATProblem ex152 = SATProblem.parseFrom("p cnf 5 6\n1 2 -3 0 1 -2 3 0 -1 2 -3 0 -1 -2 3 0 2 4 5 0 3 -4 -5 0");

    private static List<Function<SATProblem, Optional<boolean[]>>> algorithms = ImmutableList.of(
            p -> new SATAlgorithmA(p).solve(),
            p -> new SATAlgorithmB(p).solve(),
            p -> new SATAlgorithmD(p).solve(),
            p -> new SATAlgorithmL(p.to3SAT()).solve()
    );

    @Test
    public void ex7() {
        algorithms.forEach(a -> assertThat(a.apply(ex7), isPresentAndIs(new boolean[]{false, true, false, true})));
    }

    @Test
    public void ex6() {
        algorithms.forEach(a -> assertThat(a.apply(ex6), isEmpty()));
    }

    private SATProblem fromResource(String name) {
        return SATProblem.parseFrom(new InputStreamReader(this.getClass().getClassLoader().getResourceAsStream(name)));
    }

    private SATProblem knuthFromResource(String name) {
        return SATProblem.parseKnuth(new InputStreamReader(this.getClass().getClassLoader().getResourceAsStream(name)));
    }

    private final SATProblem zebra = fromResource("zebra.cnf");
    private final SATProblem quinn = fromResource("quinn.cnf");
    private final SATProblem dubois = fromResource("dubois20.cnf");
    private final SATProblem queen5 = knuthFromResource("queen-5x5-5.sat");
    private final SATProblem mutex4bitsL1 = knuthFromResource("mutex-fourbits-lemmas-1.sat");

    private String toBinaryString(boolean[] bs) {
        StringBuilder s = new StringBuilder();
        for (boolean b : bs) s.append(b ? '1' : '0');
        return s.toString();
    }

    @Test
    public void queen5() {
        algorithms.forEach(a -> assertThat(a.apply(queen5).map(queen5::evaluate), isPresentAndIs(true)));
    }

    @Test
    public void mutex4bitsL1() {
        algorithms.forEach(a -> assertThat(a.apply(mutex4bitsL1), isEmpty()));
    }

    @Test
    public void zebra() {
        algorithms.forEach(a -> assertThat(a.apply(zebra).map(zebra::evaluate), isPresentAndIs(true)));
    }

    @Test
    public void hole6() {
        SATProblem p = fromResource("hole6.cnf");
        algorithms.forEach(a -> assertThat(a.apply(p), isEmpty()));
    }

    @Test
    public void quinn() {
        algorithms.forEach(a -> assertThat(a.apply(quinn).map(quinn::evaluate), isPresentAndIs(true)));
    }

    /**
     * Generate the SAT problem waerden(j, j; n), defined by 7.2.2.2 (10), in dimacs format.
     *
     * @param j Number of consecutive 0s to require
     * @param k Number of consecutive 1s to require
     * @param n Length of binary string
     * @return the problem posed in dimacs CNF format
     */
    private SATProblem waerdenProblem(int j, int k, int n) {
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

    private int waerden(int j, int k, Function<SATProblem, AbstractSATSolver> solver) {
        // waerdenProblem(j, k, n) is satisfiable iff n < W(j, k). Compute W by finding the smallest
        // integer for which the associated problem is unsatisfiable.
        return IntStream.range(1, 1000)
                .filter(i -> !solver.apply(waerdenProblem(j, k, i)).solve().isPresent())
                .findFirst()
                .orElseThrow(() -> new IllegalStateException("did not establish Waerden value"));
    }

    // Following are a collection of values from the table of W(j, k) given on p. 5 of Fascicle 6
    @Test public void w3_3A() { assertThat(waerden(3, 3, SATAlgorithmA::new), is(9)); }
    @Test public void w3_4A() { assertThat(waerden(3, 4, SATAlgorithmA::new), is(18)); }
    @Test public void w4_3A() { assertThat(waerden(4, 3, SATAlgorithmA::new), is(18)); }
    @Test public void w4_4A() { assertThat(waerden(4, 4, SATAlgorithmA::new), is(35)); }
    @Test public void w3_6A() { assertThat(waerden(3, 6, SATAlgorithmA::new), is(32)); }
    @Test public void w4_5A() { assertThat(waerden(4, 5, SATAlgorithmA::new), is(55)); }
    @Test public void w5_4A() { assertThat(waerden(5, 4, SATAlgorithmA::new), is(55)); }
    @Test public void w6_3A() { assertThat(waerden(6, 3, SATAlgorithmA::new), is(32)); }

    //@Test public void w6_6B() { assertThat(waerden(6, 6, SATAlgorithmB::new), is(1132)); }

    @Test public void w3_3B() { assertThat(waerden(3, 3, SATAlgorithmB::new), is(9)); }
    @Test public void w3_4B() { assertThat(waerden(3, 4, SATAlgorithmB::new), is(18)); }
    @Test public void w4_3B() { assertThat(waerden(4, 3, SATAlgorithmB::new), is(18)); }
    @Test public void w4_4B() { assertThat(waerden(4, 4, SATAlgorithmB::new), is(35)); }
    @Test public void w3_6B() { assertThat(waerden(3, 6, SATAlgorithmB::new), is(32)); }
    @Test public void w4_5B() { assertThat(waerden(4, 5, SATAlgorithmB::new), is(55)); }
    @Test public void w5_4B() { assertThat(waerden(5, 4, SATAlgorithmB::new), is(55)); }
    @Test public void w6_3B() { assertThat(waerden(6, 3, SATAlgorithmB::new), is(32)); }

    @Test public void w3_3D() { assertThat(waerden(3, 3, SATAlgorithmD::new), is(9)); }
    @Test public void w3_4D() { assertThat(waerden(3, 4, SATAlgorithmD::new), is(18)); }
    @Test public void w4_3D() { assertThat(waerden(4, 3, SATAlgorithmD::new), is(18)); }
    @Test public void w4_4D() { assertThat(waerden(4, 4, SATAlgorithmD::new), is(35)); }
    @Test public void w3_6D() { assertThat(waerden(3, 6, SATAlgorithmD::new), is(32)); }
    @Test public void w4_5D() { assertThat(waerden(4, 5, SATAlgorithmD::new), is(55)); }
    @Test public void w5_4D() { assertThat(waerden(5, 4, SATAlgorithmD::new), is(55)); }
    @Test public void w6_3D() { assertThat(waerden(6, 3, SATAlgorithmD::new), is(32)); }

    @Test public void w3_3D3() { assertThat(waerden(3, 3, p -> new SATAlgorithmD(p.to3SAT())), is(9)); }
    @Test public void w3_4D3() { assertThat(waerden(3, 4, p -> new SATAlgorithmD(p.to3SAT())), is(18)); }
    @Test public void w4_3D3() { assertThat(waerden(4, 3, p -> new SATAlgorithmD(p.to3SAT())), is(18)); }
    //@Test public void w4_4D3() { assertThat(waerden(4, 4, p -> new SATAlgorithmD(p.to3SAT())), is(35)); }
    //@Test public void w3_6D3() { assertThat(waerden(3, 6, p -> new SATAlgorithmD(p.to3SAT())), is(32)); }
    //@Test public void w4_5D3() { assertThat(waerden(4, 5, p -> new SATAlgorithmD(p.to3SAT())), is(55)); }
    //@Test public void w5_4D3() { assertThat(waerden(5, 4, p -> new SATAlgorithmD(p.to3SAT())), is(55)); }
    //@Test public void w6_3D3() { assertThat(waerden(6, 3, p -> new SATAlgorithmD(p.to3SAT())), is(32)); }

    @Test public void w3_3L3() { assertThat(waerden(3, 3, p -> new SATAlgorithmL(p.to3SAT())), is(9)); }
    @Test public void w3_4L3() { assertThat(waerden(3, 4, p -> new SATAlgorithmL(p.to3SAT())), is(18)); }
    @Test public void w4_3L3() { assertThat(waerden(4, 3, p -> new SATAlgorithmL(p.to3SAT())), is(18)); }
    //@Test public void w4_4L3() { assertThat(waerden(4, 4, p -> new SATAlgorithmL(p.to3SAT())), is(35)); }
    @Test public void w3_6L3() { assertThat(waerden(3, 6, p -> new SATAlgorithmL(p.to3SAT())), is(32)); }
    //@Test public void w4_5L3() { assertThat(waerden(4, 5, p -> new SATAlgorithmL(p.to3SAT())), is(55)); }
    //@Test public void w5_4L3() { assertThat(waerden(5, 4, p -> new SATAlgorithmL(p.to3SAT())), is(55)); }
    @Test public void w6_3L3() { assertThat(waerden(6, 3, p -> new SATAlgorithmL(p.to3SAT())), is(32)); }

    @Test public void w3_3L() { assertThat(waerden(3, 3, SATAlgorithmL::new), is(9)); }

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

    private SATProblem langfordProblem(int n) {
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

    private int countTrueBits(boolean[] bs) {
        int c = 0;
        for (boolean b : bs) if (b) ++c;
        return c;
    }

    @Test
    public void langford() {
        Supplier<IntStream> range = () -> IntStream.range(2, 10);
        // The langford problem is solvable iff i mod 4 in {0, 3}. When it is solvable, we should expect the
        // number of true variables to be equal to the problem size (i.e., each digit receives exactly one
        // (dual) placement). When i mod 4 in {1, 2}, the solver should refute the problem instance.
        List<Optional<Integer>> expected = range.get().mapToObj(i -> i % 4 == 0 || i % 4 == 3 ? Optional.of(i) : Optional.<Integer>empty()).collect(Collectors.toList());
        algorithms.forEach(a -> {
            Stream<Optional<Integer>> observed = range.get().mapToObj(i -> {
                SATProblem Li = langfordProblem(i);
                return a.apply(Li).map(k -> Arrays.copyOfRange(k, 0, Li.nVariables())).map(this::countTrueBits);
            });
            assertThat(observed.collect(Collectors.toList()), is(expected));
        });
    }

    @Test
    public void langford3L() {
        SATProblem p = langfordProblem(3).to3SAT();
        assertThat(new SATAlgorithmL(p).solve().map(p::evaluate), isPresentAndIs(true));
    }

    @Test
    public void langford4L() {
        SATProblem p = langfordProblem(4).to3SAT();
        assertThat(new SATAlgorithmL(p).solve().map(p::evaluate), isPresentAndIs(true));
    }

    @Test
    public void langford4D() {
        SATProblem p = langfordProblem(4).to3SAT();
        Optional<boolean[]> sol = new SATAlgorithmD(p).solve();
        assertThat(sol.map(p::evaluate), isPresentAndIs(true));
        assertThat(sol.map(this::toBinaryString), isPresentAndIs("000010100000100001111000011110001101"));
    }

    private void threeSat(int n) {
        String vars = IntStream.range(1, n+1).mapToObj(Integer::toString).collect(Collectors.joining(" ")) + " 0";
        String cnf = String.format("p cnf %d 1\n%s\n", n, vars);
        SATProblem p = SATProblem.parseFrom(cnf);
        assertThat(p.nVariables(), is(n));
        assertThat(p.height(), is(n));
        assertThat(p.nClauses(), is(1));
        assertThat(new SATAlgorithmA(p).solve(), isPresent());
        SATProblem q = p.to3SAT();
        assertThat(q.nVariables(), is(2*n-3));
        assertThat(q.height(), is(3));
        assertThat(q.nClauses(), is(n-2));
        Optional<boolean[]> qsol = new SATAlgorithmA(q).solve();
        assertThat(qsol, isPresent());
        qsol.ifPresent(bs -> assertThat(countTrueBits(bs), is(greaterThan(0))));
    }

    @Test
    public void threeSatTest() {
        IntStream.range(4, 8).forEach(this::threeSat);
    }

    @Test
    public void unsatEvalsToFalse() {
        SATProblem l9 = langfordProblem(9);
        algorithms.forEach(a -> assertThat(a.apply(l9), isEmpty()));
        final int N = l9.nVariables();
        boolean[] v = new boolean[N];
        // Langford(9) is unsatisfiable, since 9 = 1 (mod 4). Prove every bit pattern evaluates to false.
        for (int i = 0; i < 1 << N; ++i) {
            for (int b = 0; b < N; ++b) {
                v[b] = ((i >> b) & 1) == 1;
            }
            assertThat(l9.evaluate(v), is(false));
        }
    }

    @Test
    public void algorithmL() {
        SATProblem w = waerdenProblem(3,3,8);
        assertThat(new SATAlgorithmL(w).solve().map(w::evaluate), isPresentAndIs(true));
        assertThat(new SATAlgorithmL(quinn).solve().map(quinn::evaluate), isPresentAndIs(true));
    }

    @Test
    public void dubois() {
        assertThat(new SATAlgorithmL(dubois).solve().map(dubois::evaluate), isEmpty());
        assertThat(new SATAlgorithmD(dubois).solve().map(dubois::evaluate), isEmpty());
    }
    @Test
    public void algorithmX() {
        SATProblem w = waerdenProblem(3, 3, 9);
        SATAlgorithmL a = new SATAlgorithmL(w);
        a.X();

    }

    @Test
    public void algorithmX2() {
        new SATAlgorithmL(ex152).X();
    }

    //Too hard for algorithm A or B, at least as a unit test

//    @Test
//    public void dubois20() {
//        assertThat(SATProblem.parseFrom(new InputStreamReader(this.getClass().getClassLoader().getResourceAsStream("dubois20.cnf"))).algorithmA(),
//                is(Optional.empty()));
//
//    }
}
