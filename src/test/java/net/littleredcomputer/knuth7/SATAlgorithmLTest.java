package net.littleredcomputer.knuth7;

import org.junit.Test;

import java.util.function.Function;

import static com.github.npathai.hamcrestopt.OptionalMatchers.isEmpty;
import static com.github.npathai.hamcrestopt.OptionalMatchers.isPresentAndIs;
import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertThat;

public class SATAlgorithmLTest extends SATTestBase {
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
    // TODO: get the more restricted test working and then possibly enable this or something like it
    // @Test public void w4_4_noX() { assertThat(waerden(4, 4, L3NoX), is(35)); }
    @Test public void w3_6() { assertThat(waerden(3, 6, L3), is(32)); }
    //@Test public void w3_6_noX() { assertThat(waerden(3, 6, L3NoX), is(32)); }
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
    /* @Test */ public void rand3_2062_500_314_L() { assertUNSAT(SATProblem.randomInstance(3, 2062, 500, 314), L); }

    @Test public void w_3_4_17_L() {
        SATProblem p = SATProblem.waerden(3,4,17);
        SATAlgorithmL a = new SATAlgorithmL(p.to3SAT());
        assertThat(a.solve().map(p::evaluate), isPresentAndIs(true));
    }
    @Test public void w_4_4_35_L() {
        assertThat(solveWith(L3).apply(SATProblem.waerden(4, 4, 35)), isEmpty());
    }
// TODO: We have to get this one working (and a good random test as well.)
//    @Test public void w_4_4_35_LnoX() {
//        assertThat(solveWith(L3NoX).apply(SATProblem.waerden()(4, 4, 35)), isEmpty());
//    }
    @Test public void w_4_4_35_D() {
        assertThat(solveWith(SATAlgorithmD::new).apply(SATProblem.waerden(4, 4, 35)), isEmpty());
    }

    @Test public void langford9_noX() {
        assertThat(solveWith(L3NoX).apply(SATProblem.langford(9)), isEmpty());
    }
    @Test public void langford9_L() {
        assertThat(solveWith(L).apply(SATProblem.langford(9)), isEmpty());
    }
    @Test public void langford9_D() {
        assertThat(solveWith(SATAlgorithmD::new).apply(SATProblem.langford(9)), isEmpty());
    }


    @Test public void w_3_4_13_L() {
        SATProblem p = SATProblem.waerden(3,4,13);
        SATAlgorithmL a = new SATAlgorithmL(p.to3SAT());
        assertThat(a.solve().map(p::evaluate), isPresentAndIs(true));
    }
    @Test public void w_3_4_17_D() {
        SATProblem p = SATProblem.waerden(3,4,17);
        AbstractSATSolver a = new SATAlgorithmD(p.to3SAT());
        assertThat(a.solve().map(p::evaluate), isPresentAndIs(true));
    }
    @Test public void w_3_4_13_D() {
        SATProblem p = SATProblem.waerden(3,4,13);
        SATAlgorithmD a = new SATAlgorithmD(p.to3SAT());
        assertThat(a.solve().map(p::evaluate), isPresentAndIs(true));
    }

    @Test public void lx_w339() {
        SATAlgorithmL a = new SATAlgorithmL(SATProblem.waerden(3, 3, 9));
        assertThat(a.solve(), isEmpty());
    }

    @Test public void rand_3_135_32_0() {
        SATAlgorithmL a = new SATAlgorithmL(SATProblem.randomInstance(3, 135, 32, 0));
        assertThat(a.solve(), isEmpty());
    }

    @Test public void rand_3_300_64_0() {
        SATAlgorithmL a = new SATAlgorithmL(SATProblem.randomInstance(3, 300, 64, 0));
        assertThat(a.solve(), isEmpty());
    }

    @Test public void lx_w339_noX() {
        SATAlgorithmL a = new SATAlgorithmL(SATProblem.waerden(3, 3, 9));
        a.useX = false;
        assertThat(a.solve(), isEmpty());
    }

    @Test public void rand_3_135_32_0_noX() {
        SATAlgorithmL a = new SATAlgorithmL(SATProblem.randomInstance(3, 135, 32, 0));
        a.useX = false;
        assertThat(a.solve(), isEmpty());
    }

    @Test public void rand_3_300_64_0_noX() {
        SATAlgorithmL a = new SATAlgorithmL(SATProblem.randomInstance(3, 300, 64, 0));
        a.useX = false;
        assertThat(a.solve(), isEmpty());
    }

    @Test public void rand_3_1062_250_314159() {
        SATAlgorithmL a = new SATAlgorithmL(SATProblem.randomInstance(3, 1062, 250, 314159));
        assertThat(a.solve(), isEmpty());
    }

    @Test
    public void aX2() {
        SATProblem p = SATProblem.parseKnuth("a ~b\na ~c\nc ~d\n");
        SATAlgorithmL a = new SATAlgorithmL(p);
        //a.stopAtStep = 1;
        a.solve();
    }

     //currently L takes almost 4 hours to do this (at this writing, we don't have X
    @Test public void rand3_1061_L() { testRand3_1061With(L3); }
    @Test public void rand3_1062_L() { testRand3_1062With(L3); }
}
