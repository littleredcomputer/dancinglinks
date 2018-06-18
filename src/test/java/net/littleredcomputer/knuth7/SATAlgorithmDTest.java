package net.littleredcomputer.knuth7;

import org.junit.Test;

import java.util.function.Function;

import static com.github.npathai.hamcrestopt.OptionalMatchers.isEmpty;
import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertThat;

public class SATAlgorithmDTest extends SATTestBase {
    private Function<SATProblem, AbstractSATSolver> D = SATAlgorithmD::new;

    @Test public void ex6() { testEx6With(D); }
    @Test public void ex7() { testEx7With(D); }

    @Test public void w3_3() { assertThat(waerden(3, 3, D), is(9)); }
    @Test public void w3_4() { assertThat(waerden(3, 4, D), is(18)); }
    @Test public void w4_3() { assertThat(waerden(4, 3, D), is(18)); }
    @Test public void w4_4() { assertThat(waerden(4, 4, D), is(35)); }
    @Test public void w3_6() { assertThat(waerden(3, 6, D), is(32)); }
    @Test public void w4_5() { assertThat(waerden(4, 5, D), is(55)); }
    @Test public void w5_4() { assertThat(waerden(5, 4, D), is(55)); }
    @Test public void w6_3() { assertThat(waerden(6, 3, D), is(32)); }

    @Test public void w3_3_3sat() { assertThat(waerden(3, 3, D.compose(SATProblem::to3SAT)), is(9)); }
    @Test public void w3_4_3sat() { assertThat(waerden(3, 4, D.compose(SATProblem::to3SAT)), is(18)); }
    @Test public void w4_3_3sat() { assertThat(waerden(4, 3, D.compose(SATProblem::to3SAT)), is(18)); }

    @Test public void langford() { testLangfordWith(D); }
    @Test public void hole6() { testHole6With(D); }
    @Test public void dubois() { testDuboisWith(D); }
    @Test public void testQueen5() { testQueen5With(D); }
    @Test public void testMutex4BitsL1() { testMutex4BitsL1With(D); }
    @Test public void testZebra() { testZebraWith(D); }
    @Test public void testQuinn() { testQuinnWith(D); }

    @Test public void rand3_420_100_0_D() { assertThat(D.apply(rand3_420_100_0).solve(), isEmpty()); }
}
