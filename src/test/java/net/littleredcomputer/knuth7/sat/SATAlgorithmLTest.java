package net.littleredcomputer.knuth7.sat;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.junit.Test;

import java.util.EnumSet;
import java.util.Optional;
import java.util.function.Function;

import static com.github.npathai.hamcrestopt.OptionalMatchers.isEmpty;
import static com.github.npathai.hamcrestopt.OptionalMatchers.isPresentAndIs;
import static org.hamcrest.CoreMatchers.either;
import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertThat;

public class SATAlgorithmLTest extends SATTestBase {
    private static final Logger log = LogManager.getFormatterLogger();
    private final Function<SATProblem, AbstractSATSolver> L = SATAlgorithmL3::new; /* XXX change to: SATAlgorithmL::New */
    private final Function<SATProblem, AbstractSATSolver> L3 = L.compose(SATProblem::to3SAT);
    private final Function<SATProblem, AbstractSATSolver> L3NoX = p -> {
        SATAlgorithmL a = new SATAlgorithmL3(p.to3SAT());
        a.useX = false;
        return a;
    };
    private final Function<SATProblem, AbstractSATSolver> L3NoY = p -> {
        SATAlgorithmL a = new SATAlgorithmL3(p.to3SAT());
        a.useY = false;
        return a;
    };
    private final Function<SATProblem, AbstractSATSolver> LXnoX = p -> {
        SATAlgorithmL a = new SATAlgorithmLX(p);
        a.useX = false;
        return a;
    };

    @Test public void w3_3() { assertThat(waerden(3, 3, L), is(9)); }

    @Test public void w3_3_noX() { assertThat(waerden(3, 3, L3NoX), is(9)); }
    @Test public void w3_4() { assertThat(waerden(3, 4, L3), is(18)); }
    @Test public void w3_4_noX() { assertThat(waerden(3, 4, L3NoX), is(18)); }
    @Test public void w3_4_noY() { assertThat(waerden(3, 4, L3NoY), is(18)); }
    @Test public void w4_3() { assertThat(waerden(4, 3, L3), is(18)); }
    @Test public void w4_4() { assertThat(waerden(4, 4, L3), is(35)); }
    @Test public void w3_6() { assertThat(waerden(3, 6, L3), is(32)); }
    @Test public void w3_7() { assertThat(waerden(3, 7, L3), is(46)); }
    @Test public void w3_8() { assertThat(waerden(3, 8, L3), is(58)); }
    @Test public void w4_5() { assertThat(waerden(4, 5, L3), is(55)); }
    @Test public void w5_4() { assertThat(waerden(5, 4, L3), is(55)); }
    @Test public void w6_3() { assertThat(waerden(6, 3, L3), is(32)); }
    @Test public void w7_3() { assertThat(waerden(7, 3, L3), is(46)); }
    @Test public void w8_3() { assertThat(waerden(8, 3, L3), is(58)); }
    // These are do-able with L3, but take around 30s
    /* @Test */ public void w6_4() { assertThat(waerden(6, 4, L3), is(73)); }
    /* @Test */ public void w4_6() { assertThat(waerden(4, 6, L3), is(73)); }

    @Test public void hole6() { testHole6With(L3); }
    @Test public void dubois() { testDuboisWith(L); }
    @Test public void testQueen5() { testQueen5With(L3); }
    @Test public void testMutex4BitsL1() { testMutex4BitsL1With(L3); }
    @Test public void testZebra() { testZebraWith(L3); }
    @Test public void testQuinn() { testQuinnWith(L); }
    @Test public void ex6() { testEx6With(L); }
    @Test public void ex7() { testEx7With(L); }
    @Test public void rand3_1061_L() { testRand3_1061With(L); }
    @Test public void rand3_1062_L() { testRand3_1062With(L); }
    @Test public void langford() { testLangfordWith(L3); }


    @Test public void w3_3_XnoX() {
        // SATAlgorithmL s = new SATAlgorithmLX(SATProblem.waerden(3, 3, 9));
        SATAlgorithmL s = new SATAlgorithmL3(SATProblem.waerden(3, 3, 9));
        s.useX = false;
        s.tracing = EnumSet.allOf(SATAlgorithmL.Trace.class);
        assertThat(s.solve(), isEmpty());
    }


    // This one still takes a long time
    /* @Test */ public void rand3_2062_500_314_L() { assertUNSAT(SATProblem.randomInstance(3, 2062, 500, 314), L); }

    @Test public void w_3_4_17() {
        SATProblem p = SATProblem.waerden(3,4,17);
        SATAlgorithmL a = new SATAlgorithmL3(p.to3SAT());
        a.trackChoices = true;
        assertThat(a.solve().map(p::evaluate), isPresentAndIs(true));
        // This is sort of delicate but getting all the computations working in the same way
        // Knuth's model implementation does took a lot of effort. The sequence of variable choices,
        // backtrack points etc. are sensitive to the details of the implementation. This sequence
        // has been hand-checked to correspond with sat11.w's choices.
        assertThat(a.track(), is("[~9, 9, ~8, 8, null, null]"));
    }

    @Test public void w_3_4_17_noY() {
        SATProblem p = SATProblem.waerden(3,4,17);
        SATAlgorithmL a = new SATAlgorithmL3(p.to3SAT());
        a.useY = false;
        a.trackChoices = true;
        assertThat(a.solve().map(p::evaluate), isPresentAndIs(true));
        assertThat(a.track(), is("[~9, 15, ~15, 9, ~8, 8, ~7, null, null]"));
    }

    @Test public void rand3_420_100_0_L() {
        SATAlgorithmL a = new SATAlgorithmL3(rand3_420_100_0);
        a.trackChoices = true;
        assertThat(a.solve().map(rand3_420_100_0::evaluate), isEmpty());
        assertThat(a.track(), is("[3, 42, ~84, 52, ~52, 84, ~11, 11, ~42, 40, ~40, ~3, 63, 34, 2, ~2, ~34, ~63]"));
    }

    @Test public void rand3_420_100_0_LnoY() {
        SATAlgorithmL a = new SATAlgorithmL3(rand3_420_100_0);
        a.trackChoices = true;
        a.useY = false;
        assertThat(a.solve().map(rand3_420_100_0::evaluate), isEmpty());
        assertThat(a.track(), is("[3, 42, ~84, 61, 52, ~52, ~26, 26, ~61, 84, ~11, 40, ~40, 11," +
                " ~14, 14, ~42, ~6, 40, 4, 52, 65, ~65, ~52, ~4, ~40, 6, 2, ~2, ~3, ~94, 94]"));
    }

    @Test public void w_4_4_35() {
        assertThat(solveWith(L3).apply(SATProblem.waerden(4, 4, 35)), isEmpty());
    }
    @Test public void w_4_4_34() {
        SATProblem p = SATProblem.waerden(4, 4, 34).to3SAT();
        SATAlgorithmL a = new SATAlgorithmL3(p);
        a.useY = true;
        assertThat(a.solve().map(p::evaluate), isPresentAndIs(true));
    }

    @Test public void rand_3_32_9_2010_noX() {
        assertThat(solveWith(L3NoX).apply(SATProblem.randomInstance(3,32,9,2010)), isPresentAndIs(true));
    }

    @Test public void w_3_4_13_L() {
        SATProblem p = SATProblem.waerden(3,4,13);
        SATAlgorithmL a = new SATAlgorithmL3(p.to3SAT());
        assertThat(a.solve().map(p::evaluate), isPresentAndIs(true));
    }
    @Test public void w338() { assertThat(solveWith(L).apply(SATProblem.waerden(3, 3, 8)), isPresentAndIs(true)); }
    @Test public void w339() { assertThat(solveWith(L).apply(SATProblem.waerden(3, 3, 9)), isEmpty()); }
    @Test public void rand_3_135_32_0() { assertThat(solveWith(L).apply(SATProblem.randomInstance(3, 135, 32, 0)), isEmpty()); }
    @Test public void rand_3_300_64_0() { assertThat(solveWith(L).apply(SATProblem.randomInstance(3, 300, 64, 0)), isEmpty()); }
    @Test public void w339_noX() { assertThat(solveWith(L3NoX).apply(SATProblem.waerden(3, 3, 9)), isEmpty()); }
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

    /* a minimal example I used to chase a bug. */
    @Test public void rand_3_13_7_617() {
        SATProblem p = SATProblem.randomInstance(3, 13, 7, 617);
        SATAlgorithmL a = new SATAlgorithmL3(p);
        assertThat(a.solve().map(p::evaluate), isPresentAndIs(true));
    }

    @Test public void manySmallRandomInstances() {
        final int k = 3, m = 640, n = 150, N = 250;
        int unsat = 0, sat = 0;
        for (int i = 0; i < N; ++i) {
            Optional<Boolean> a = solveWith(L).apply(SATProblem.randomInstance(k, m, n, i));
            assertThat(a, is(either(isPresentAndIs(true)).or(isEmpty())));
            if (a.isPresent()) ++sat; else ++unsat;
        }
        log.info("After %d tests %d sat %d unsat", N, sat, unsat);
    }

    @Test
    public void aX2() {
        SATProblem p = SATProblem.parseKnuth("a ~b\na ~c\nc ~d\n");
        SATAlgorithmL a = new SATAlgorithmL3(p);
        //a.stopAtStep = 1;
        a.solve();
    }
}
