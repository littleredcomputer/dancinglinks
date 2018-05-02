package net.littleredcomputer.knuth7;

import org.hamcrest.Matcher;
import org.junit.Test;

import java.util.Arrays;
import java.util.List;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.DoubleStream;

import static java.util.stream.Collectors.toList;
import static org.hamcrest.CoreMatchers.is;
import static org.hamcrest.Matchers.contains;
import static org.hamcrest.number.IsCloseTo.closeTo;
import static org.junit.Assert.assertThat;

public class SATAlgorithmLTest extends TestProblems {
    private Function<SATProblem, AbstractSATSolver> L = SATAlgorithmL::new;
    private Function<SATProblem, AbstractSATSolver> L3 = L.compose(SATProblem::to3SAT);

    @Test public void ex6() { testEx6With(L); }
    @Test public void ex7() { testEx7With(L); }

    @Test public void w3_3() { assertThat(waerden(3, 3, L), is(9)); }
    @Test public void w3_4() { assertThat(waerden(3, 4, L3), is(18)); }
    @Test public void w4_3() { assertThat(waerden(4, 3, L3), is(18)); }
    //@Test public void w4_4() { assertThat(waerden(4, 4, L3), is(35)); }
    @Test public void w3_6() { assertThat(waerden(3, 6, L3), is(32)); }
    //@Test public void w4_5() { assertThat(waerden(4, 5, L3), is(55)); }
    //@Test public void w5_4() { assertThat(waerden(5, 4, L3), is(55)); }
    @Test public void w6_3() { assertThat(waerden(6, 3, L3), is(32)); }

    @Test public void langford() { testLangfordWith(L3); }
    @Test public void hole6() { testHole6With(L3); }
    @Test public void dubois() { testDuboisWith(L); }
    @Test public void testQueen5() { testQueen5With(L3); }
    @Test public void testMutex4BitsL1() { testMutex4BitsL1With(L3); }
    @Test public void testZebra() { testZebraWith(L3); }
    @Test public void testQuinn() { testQuinnWith(L); }

    @Test public void rand3_420_100_0_L() { assertUNSAT(rand3_420_100_0, L); }

    @Test
    public void algorithmX() {
        SATProblem w = waerdenProblem(3, 3, 9);
        SATAlgorithmL a = new SATAlgorithmL(w);
        a.useX = true;
        a.stopAtStep = 0;
        a.solve();
        a.x.computeHeuristics();

        List<Matcher<? super Double>> expectedHValues = DoubleStream.of(
                0.0, 4.847, 4.562, 6.628, 6.616, 8.234, 6.616, 6.628, 4.562, 4.847)
                .flatMap(d -> DoubleStream.of(d, d))
                .mapToObj(d -> closeTo(d, 0.05))
                .collect(toList());

        assertThat(Arrays.stream(a.x.h[0]).boxed().collect(Collectors.toList()),  contains(expectedHValues));
        a.stopAtStep = -1;
        a.solve();
    }

    @Test
    public void aX2() {
        SATProblem p = SATProblem.parseKnuth("a ~b\na ~c\nc ~d\n");
        SATAlgorithmL a = new SATAlgorithmL(p);
        a.useX = true;
        //a.stopAtStep = 1;
        a.solve();
    }

    // currently L takes almost 4 hours to do this (at this writing, we don't have X
    //    @Test
    //    public void rand3_1061_L() {
    //        assertThat(new SATAlgorithmL(rand3_1061).solve().map(rand3_1061::evaluate), isPresentAndIs(true));
    //    }
}
