package net.littleredcomputer.knuth7;

import org.junit.Test;

import java.io.InputStreamReader;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import static com.github.npathai.hamcrestopt.OptionalMatchers.isPresentAndIs;
import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.*;

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

    @Test
    public void ex7() {
        assertThat(SATProblem.parseFrom(new StringReader("p cnf 4 7\n1 2 -3 0 2 3 -4 0 3 4 1 0 4 -1 2 0 -1 -2 3 0 -2 -3 4 0 -3 -4 -1 0")).algorithmA(),
                isPresentAndIs(new boolean[]{false, true, false, true}));
    }

    @Test
    public void ex6() {
        assertThat(SATProblem.parseFrom(new StringReader("p cnf 4 8\n1 2 -3 0 2 3 -4 0 3 4 1 0 4 -1 2 0 -1 -2 3 0 -2 -3 4 0 -3 -4 -1 0 -4 1 -2 0")).algorithmA(),
                is(Optional.empty()));
    }

    private SATProblem fromResource(String name) {
        return SATProblem.parseFrom(new InputStreamReader(this.getClass().getClassLoader().getResourceAsStream(name)));
    }

    private String toBinaryString(boolean[] bs) {
        StringBuilder s = new StringBuilder();
        for (boolean b : bs) s.append(b ? '1' : '0');
        return s.toString();
    }

    @Test
    public void zebra() {
        assertThat(fromResource("zebra.cnf").algorithmA().map(this::toBinaryString),
                isPresentAndIs("00100000011000000010010000000110000000100100000100100000100000010001000000110000010000010000010000010000110000000100010001000001000000001010010000011010010"));
    }

    @Test
    public void hole6() {
        assertThat(fromResource("hole6.cnf").algorithmA(), is(Optional.empty()));
    }

    @Test
    public void quinn() {
        assertThat(fromResource("quinn.cnf").algorithmA().map(this::toBinaryString),
                isPresentAndIs("1010111110111001"));
    }

    /**
     * Generate the SAT problem waerden(j, j; n), defined by 7.2.2.2 (10), in dimacs format.
     *
     * @param j Number of consecutive 0s to require
     * @param k Number of consecutive 1s to require
     * @param n Length of binary string
     * @return the problem posed in dimacs CNF format
     */
    private String waerdenProblem(int j, int k, int n) {
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
        return "c waerden(" + j + ", " + k + ", " + n + ")\np cnf " + n + ' ' + clauseCount + '\n' + clauses;
    }

    private int waerden(int j, int k) {
        // waerdenProblem(j, k, n) is satisfiable iff n < W(j, k). Compute W by finding the smallest
        // integer for which the associated problem is unsatisfiable.
        return IntStream.range(1, 1000)
                .filter(i -> !SATProblem.parseFrom(new StringReader(waerdenProblem(j, k, i))).algorithmA().isPresent())
                .findFirst()
                .getAsInt();
    }

    // Following are a collection of values from the table of W(j, k) given on p. 5 of Fascicle 6
    @Test public void w3_3() { assertThat(waerden(3, 3), is(9)); }
    @Test public void w3_4() { assertThat(waerden(3, 4), is(18)); }
    @Test public void w4_3() { assertThat(waerden(4, 3), is(18)); }
    @Test public void w4_4() { assertThat(waerden(4, 4), is(35)); }
    @Test public void w3_6() { assertThat(waerden(3, 6), is(32)); }
    @Test public void w4_5() { assertThat(waerden(4, 5), is(55)); }
    @Test public void w5_4() { assertThat(waerden(5, 4), is(55)); }
    @Test public void w6_3() { assertThat(waerden(6, 3), is(32)); }

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

    private String langfordProblem(int n) {
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
                ++row;
            }
        }
        int nClauses = 0;
        StringBuilder sb = new StringBuilder();
        for (List<Boolean> c : columns) nClauses += S1(c, sb);
        return "c langford(" + n + ")\np cnf " + row + ' ' + nClauses + "\n" + sb;
    }

    @Test
    public void langford() {
        Function<boolean[], Integer> countTrueBits = bs -> {
            int c = 0;
            for (boolean b : bs) if (b) ++c;
            return c;
        };
        Supplier<IntStream> range = () -> IntStream.range(2, 10);
        // The langford problem is solvable iff i mod 4 in {0, 3}. When it is solvable, we should expect the
        // number of true variables to be equal to the problem size (i.e., each digit receives exactly one
        // (dual) placement). When i mod 4 in {1, 2}, the solver should refute the problem instance.
        Stream<Optional<Integer>> expected = range.get().mapToObj(i -> i % 4 == 0 || i % 4 == 3 ? Optional.of(i) : Optional.empty());
        Stream<Optional<Integer>> observed = range.get().mapToObj(i -> SATProblem.parseFrom(new StringReader(langfordProblem(i)))
                .algorithmA()
                .map(countTrueBits));
        assertThat(expected.collect(Collectors.toList()), is(observed.collect(Collectors.toList())));
    }

    @Test
    public void langford3() {
        assertThat(SATProblem.parseFrom(new StringReader(langfordProblem(3))).algorithmA().map(this::toBinaryString), isPresentAndIs("001010001"));
    }

    @Test
    public void langford4() {
        assertThat(SATProblem.parseFrom(new StringReader(langfordProblem(4))).algorithmA().map(this::toBinaryString), isPresentAndIs("000010100000100001"));
    }

    // Too hard for algorithm A
    //    @Test
    //    public void dubois20() {
    //        assertThat(SATProblem.parseFrom(new InputStreamReader(this.getClass().getClassLoader().getResourceAsStream("dubois20.cnf"))).algorithmA(),
    //                is(Optional.empty()));
    //
    //    }

}

