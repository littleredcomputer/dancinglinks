package net.littleredcomputer.knuth7;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.Test;

import java.util.Optional;
import java.util.function.Function;

import static com.github.npathai.hamcrestopt.OptionalMatchers.isEmpty;
import static com.github.npathai.hamcrestopt.OptionalMatchers.isPresentAndIs;
import static org.hamcrest.CoreMatchers.either;
import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertThat;

public class SATAlgorithmLTest extends SATTestBase {
    private static final Logger log = LogManager.getFormatterLogger();
    private Function<SATProblem, AbstractSATSolver> L = SATAlgorithmL::new;
    private Function<SATProblem, AbstractSATSolver> L3 = L.compose(SATProblem::to3SAT);
    private Function<SATProblem, AbstractSATSolver> L3NoX = p -> {
        SATAlgorithmL a = new SATAlgorithmL(p.to3SAT());
        a.useX = false;
        return a;
    };

    @Test public void ex6() { testEx6With(L); }
    @Test public void ex7() { testEx7With(L); }

    @Test public void w3_3() { assertThat(waerden(3, 3, L), is(9)); }
    @Test public void w3_3_noX() { assertThat(waerden(3, 3, L3NoX), is(9)); }
    @Test public void w3_4() { assertThat(waerden(3, 4, L3), is(18)); }
    @Test public void w3_4_noX() { assertThat(waerden(3, 4, L3NoX), is(18)); }
    @Test public void w4_3() { assertThat(waerden(4, 3, L3), is(18)); }
    @Test public void w4_4() { assertThat(waerden(4, 4, L3), is(35)); }
    @Test public void w3_6() { assertThat(waerden(3, 6, L3), is(32)); }
    @Test public void w4_5() { assertThat(waerden(4, 5, L3), is(55)); }
    @Test public void w5_4() { assertThat(waerden(5, 4, L3), is(55)); }
    @Test public void w6_3() { assertThat(waerden(6, 3, L3), is(32)); }

    @Test public void langford() { testLangfordWith(L3); }
    @Test public void hole6() { testHole6With(L3); }
    @Test public void dubois() { testDuboisWith(L); }
    @Test public void testQueen5() { testQueen5With(L3); }
    @Test public void testMutex4BitsL1() { testMutex4BitsL1With(L3); }
    @Test public void testZebra() { testZebraWith(L3); }
    @Test public void testQuinn() { testQuinnWith(L); }


    // This one still takes a long time
    /* @Test */ public void rand3_2062_500_314_L() { assertUNSAT(SATProblem.randomInstance(3, 2062, 500, 314), L); }

    @Test public void w_3_4_17() {
        SATProblem p = SATProblem.waerden(3,4,17);
        SATAlgorithmL a = new SATAlgorithmL(p.to3SAT());
        a.trackChoices = true;
        assertThat(a.solve().map(p::evaluate), isPresentAndIs(true));
        // This is sort of delicate but getting all the computations working in the same way
        // Knuth's model implementation does took a lot of effort. The sequence of variable choices,
        // backtrack points etc. are sensitive to the details of the implementation. This sequence
        // has been hand-checked to correspond with sat11.w's choices.
        assertThat(a.track.toString(), is("[~9, 15, ~15, 9, ~8, 8, ~7, null, null]"));
    }

    @Test public void rand3_420_100_0_L() {
        SATAlgorithmL a = new SATAlgorithmL(rand3_420_100_0);
        a.trackChoices = true;
        assertThat(a.solve().map(rand3_420_100_0::evaluate), isEmpty());
        assertThat(a.track.toString(), is("[3, 42, ~84, 61, 52, ~52, ~26, 26, ~61, 84, ~11, 40, ~40, 11, ~14, 14, ~42, ~6, 40, 4, 52, 65, ~65, ~52, ~4, ~40, 6, 2, ~2, ~3, ~94, 94]"));
    }

    @Test public void w_4_4_35() {
        assertThat(solveWith(L3).apply(SATProblem.waerden(4, 4, 35)), isEmpty());
    }

    // This passes, but takes ~ 4 minutes */
    /* @Test */ public void w_4_4_35_LnoX() { assertThat(solveWith(L3NoX).apply(SATProblem.waerden(4, 4, 35)), isEmpty()); }

    @Test public void langford9_noX() {
        assertThat(solveWith(L3NoX).apply(SATProblem.langford(9)), isEmpty());
    }
    @Test public void langford9_L() {
        assertThat(solveWith(L3).apply(SATProblem.langford(9)), isEmpty());
    }

    @Test public void w_3_4_13_L() {
        SATProblem p = SATProblem.waerden(3,4,13);
        SATAlgorithmL a = new SATAlgorithmL(p.to3SAT());
        assertThat(a.solve().map(p::evaluate), isPresentAndIs(true));
    }
    @Test public void lx_w339() { assertThat(solveWith(L).apply(SATProblem.waerden(3, 3, 9)), isEmpty()); }
    @Test public void rand_3_135_32_0() { assertThat(solveWith(L).apply(SATProblem.randomInstance(3, 135, 32, 0)), isEmpty()); }
    @Test public void rand_3_300_64_0() { assertThat(solveWith(L).apply(SATProblem.randomInstance(3, 300, 64, 0)), isEmpty()); }
    @Test public void lx_w339_noX() { assertThat(solveWith(L3NoX).apply(SATProblem.waerden(3, 3, 9)), isEmpty()); }
    @Test public void rand_3_135_32_0_noX() { assertThat(solveWith(L3NoX).apply(SATProblem.randomInstance(3, 135, 32, 0)), isEmpty()); }
    @Test public void rand_3_300_64_0_noX() { assertThat(solveWith(L3NoX).apply(SATProblem.randomInstance(3, 300, 64, 0)), isEmpty()); }

    @Test public void manyTinyRandomInstancesNoX() {
        final int k = 3, m = 64, n = 15;
        for (int i = 0; i < 1000; ++i) {
            Optional<Boolean> a = solveWith(L3NoX).apply(SATProblem.randomInstance(k, m, n, i));
            log.info("Random SAT test %d %d %d %d -> %s", k, m, n, i, a.map(b -> b ? "SAT" : "BROKEN").orElse("UNSAT"));
            assertThat(a, is(either(isPresentAndIs(true)).or(isEmpty())));
        }
    }

    @Test public void manySmallRandomInstances() {
        final int k = 3, m = 640, n = 150;
        for (int i = 0; i < 250; ++i) {
            Optional<Boolean> a = solveWith(L).apply(SATProblem.randomInstance(k, m, n, i));
            log.info("Random SAT test %d %d %d %d -> %s", k, m, n, i, a.map(b -> b ? "SAT" : "BROKEN").orElse("UNSAT"));
            assertThat(a, is(either(isPresentAndIs(true)).or(isEmpty())));
        }
    }

    @Test
    public void aX2() {
        SATProblem p = SATProblem.parseKnuth("a ~b\na ~c\nc ~d\n");
        SATAlgorithmL a = new SATAlgorithmL(p);
        //a.stopAtStep = 1;
        a.solve();
    }

    @Test public void rand3_1061_L() { testRand3_1061With(L); }
    @Test public void rand3_1062_L() { testRand3_1062With(L); }
}
