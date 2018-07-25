package net.littleredcomputer.knuth7.sat;

import com.google.common.collect.ImmutableList;
import org.junit.Test;

import java.io.StringReader;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static com.github.npathai.hamcrestopt.OptionalMatchers.isEmpty;
import static com.github.npathai.hamcrestopt.OptionalMatchers.isPresent;
import static java.util.stream.Collectors.toSet;
import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.Matchers.contains;
import static org.junit.Assert.assertThat;

public class SATProblemTest extends SATTestBase {

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
    public void randomInstanceTest() {
        // To test the random instance generation, we verify that our results agree with
        // Knuth's example rand-3-1061-250-314159.sat (except our variables are 1-based,
        // and his are 0-based)
        SATProblem r = SATProblem.randomInstance(3, 1061, 250, 314159);
        assertThat(r.width(), is(3));
        assertThat(r.nClauses(), is(1061));
        assertThat(r.nVariables(), is(250));
        assertThat(r.getClause(0), contains(-165, 123, 90));
        assertThat(r.getClause(1060), contains(172, 93, 30));
    }

    private static final List<Function<SATProblem, Optional<boolean[]>>> algorithms = ImmutableList.of(
            p -> new SATAlgorithmA(p).solve(),
            p -> new SATAlgorithmB(p).solve(),
            p -> new SATAlgorithmD(p).solve(),
            p -> new SATAlgorithmL3(p.to3SAT()).solve()
    );

    private void threeSat(int n) {
        String vars = IntStream.range(1, n+1).mapToObj(Integer::toString).collect(Collectors.joining(" ")) + " 0";
        String cnf = String.format("p cnf %d 1\n%s\n", n, vars);
        SATProblem p = SATProblem.parseFrom(cnf);
        assertThat(p.nVariables(), is(n));
        assertThat(p.width(), is(n));
        assertThat(p.nClauses(), is(1));
        assertThat(new SATAlgorithmA(p).solve(), isPresent());
        SATProblem q = p.to3SAT();
        assertThat(q.nVariables(), is(2*n-3));
        assertThat(q.width(), is(3));
        assertThat(q.nClauses(), is(n-2));
        Optional<boolean[]> qsol = new SATAlgorithmA(q).solve();
        assertThat(qsol.map(q::evaluate), isPresent());
    }

    @Test
    public void threeSatTest() {
        IntStream.range(4, 8).forEach(this::threeSat);
    }

    @Test
    public void unsatEvalsToFalse() {
        SATProblem l9 = SATProblem.langford(9);
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
    public void smallRandomTestAgreement() {
        for (int seed = 0; seed < 1000; ++seed) {
            SATProblem p = SATProblem.randomInstance(3, 13, 7, seed);
            // Partition the results of the various algorithms into equivalence classes. There can be only one.
            // We confess, however, that we are only testing that all the algorithms agree on the satisfiability
            // of the random problems and not the satisfying assignments themselves (of which there may be more
            // than one for satisfiable instances: different algorithms may find different variable assignments).
            System.out.printf("trying seed %d\n", seed);
            assertThat(algorithms.stream().map(a -> a.apply(p).map(p::evaluate))
                    .collect(Collectors.collectingAndThen(toSet(), Set::size)), is(1));
        }
    }
}
