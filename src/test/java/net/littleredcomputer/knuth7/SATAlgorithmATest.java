package net.littleredcomputer.knuth7;

import org.junit.Test;

import java.util.function.Function;

import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertThat;

public class SATAlgorithmATest extends SATTestBase {
    private Function<SATProblem, AbstractSATSolver> A = SATAlgorithmA::new;

    @Test public void ex6() { testEx6With(A); }
    @Test public void ex7() { testEx7With(A); }

    @Test public void w3_3() { assertThat(waerden(3, 3, A), is(9)); }
    @Test public void w3_4() { assertThat(waerden(3, 4, A), is(18)); }
    @Test public void w4_3() { assertThat(waerden(4, 3, A), is(18)); }
    @Test public void w4_4() { assertThat(waerden(4, 4, A), is(35)); }
    @Test public void w3_6() { assertThat(waerden(3, 6, A), is(32)); }
    @Test public void w4_5() { assertThat(waerden(4, 5, A), is(55)); }
    @Test public void w5_4() { assertThat(waerden(5, 4, A), is(55)); }
    @Test public void w6_3() { assertThat(waerden(6, 3, A), is(32)); }

    @Test public void langford() { testLangfordWith(A); }
    @Test public void hole6() { testHole6With(A); }
    @Test public void testQueen5() { testQueen5With(A); }
    @Test public void testMutex4BitsL1() { testMutex4BitsL1With(A); }
    @Test public void testZebra() { testZebraWith(A); }
    @Test public void testQuinn() { testQuinnWith(A); }
}
