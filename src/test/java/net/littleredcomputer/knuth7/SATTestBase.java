package net.littleredcomputer.knuth7;

import com.github.npathai.hamcrestopt.OptionalMatchers;
import com.google.common.primitives.Booleans;
import org.hamcrest.CoreMatchers;
import org.junit.Assert;

import java.io.InputStreamReader;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import static java.util.stream.Collectors.toList;

public class SATTestBase {
    int waerden(int j, int k, Function<SATProblem, AbstractSATSolver> solver) {
        // waerdenProblem(j, k, n) is satisfiable iff n < W(j, k). Compute W by finding the smallest
        // integer for which the associated problem is unsatisfiable.
        return IntStream.range(1, 1000)
                .filter(i -> !solver.apply(SATProblem.waerden(j, k, i)).solve().isPresent())
                .findFirst()
                .orElseThrow(() -> new IllegalStateException("did not establish Waerden value"));
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

    private static SATProblem fromResource(String name) {
        return SATProblem.parseFrom(new InputStreamReader(SATTestBase.class.getClassLoader().getResourceAsStream(name)));
    }

    private static SATProblem knuthFromResource(String name) {
        return SATProblem.parseKnuth(new InputStreamReader(SATTestBase.class.getClassLoader().getResourceAsStream(name)));
    }

    void testHole6With(Function<SATProblem, AbstractSATSolver> a) { assertUNSAT(hole6, a); }
    void testDuboisWith(Function<SATProblem, AbstractSATSolver> a) { assertUNSAT(dubois, a); }
    void testQueen5With(Function<SATProblem, AbstractSATSolver> a) { assertSAT(queen5, a); }
    void testMutex4BitsL1With(Function<SATProblem, AbstractSATSolver> a) { assertUNSAT(mutex4bitsL1, a); }
    void testZebraWith(Function<SATProblem, AbstractSATSolver> a) { assertSAT(zebra, a); }
    void testQuinnWith(Function<SATProblem, AbstractSATSolver> a) { assertSAT(quinn, a); }
    void testEx6With(Function<SATProblem, AbstractSATSolver> a) { assertUNSAT(ex6, a); }
    void testEx7With(Function<SATProblem, AbstractSATSolver> a) { assertSAT(ex7, a); }
    void testRand3_1061With(Function<SATProblem, AbstractSATSolver> a) { assertSAT(rand3_1061, a); }
    void testRand3_1062With(Function<SATProblem, AbstractSATSolver> a) { assertUNSAT(rand3_1062, a); }

    void assertSAT(SATProblem p, Function<SATProblem, AbstractSATSolver> a) {
        Assert.assertThat(a.apply(p).solve().map(p::evaluate), OptionalMatchers.isPresentAndIs(true));
    }

    void assertUNSAT(SATProblem p, Function<SATProblem, AbstractSATSolver> a) {
        Assert.assertThat(a.apply(p).solve(), OptionalMatchers.isEmpty());
    }

    public void testLangfordWith(Function<SATProblem, AbstractSATSolver> a) {
        Supplier<IntStream> range = () -> IntStream.range(2, 10);
        // The langford problem is solvable iff i mod 4 in {0, 3}. When it is solvable, we should expect the
        // number of true variables to be equal to the problem size (i.e., each digit receives exactly one
        // (dual) placement). When i mod 4 in {1, 2}, the solver should refute the problem instance.
        List<Optional<Integer>> expected = range.get().mapToObj(i -> i % 4 == 0 || i % 4 == 3 ? Optional.of(i) : Optional.<Integer>empty()).collect(toList());
        Stream<Optional<Integer>> observed = range.get().mapToObj(i -> {
            SATProblem Li = SATProblem.langford(i);
            return a.apply(Li).solve()
                    .map(k -> Arrays.copyOfRange(k, 0, Li.nVariables()))
                    .map(Booleans::asList)
                    .map(bs -> bs.stream().mapToInt(b -> b ? 1 : 0).sum());
        });
        Assert.assertThat(observed.collect(toList()), CoreMatchers.is(expected));
    }

    // Compose a solver factory with an evaluation step to create a one-step solution function
    Function<SATProblem, Optional<Boolean>> solveWith(Function<SATProblem, AbstractSATSolver> s) {
        return p -> s.apply(p).solve().map(p::evaluate);
    }
}
