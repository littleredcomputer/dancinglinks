package net.littleredcomputer.knuth7;

import org.junit.Test;

import java.util.function.Function;

import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertThat;

public class SATAlgorithmBTest extends SATTestBase {
    private final Function<SATProblem, AbstractSATSolver> B = SATAlgorithmB::new;

    @Test public void ex6() { testEx6With(B); }
    @Test public void ex7() { testEx7With(B); }

    @Test public void w3_3() { assertThat(waerden(3, 3, B), is(9)); }
    @Test public void w3_4() { assertThat(waerden(3, 4, B), is(18)); }
    @Test public void w4_3() { assertThat(waerden(4, 3, B), is(18)); }
    @Test public void w4_4() { assertThat(waerden(4, 4, B), is(35)); }
    @Test public void w3_6() { assertThat(waerden(3, 6, B), is(32)); }
    @Test public void w4_5() { assertThat(waerden(4, 5, B), is(55)); }
    @Test public void w5_4() { assertThat(waerden(5, 4, B), is(55)); }
    @Test public void w6_3() { assertThat(waerden(6, 3, B), is(32)); }

    @Test public void langford() { testLangfordWith(B); }
    @Test public void hole6() { testHole6With(B); }
    @Test public void testQueen5() { testQueen5With(B); }
    @Test public void testMutex4BitsL1() { testMutex4BitsL1With(B); }
    @Test public void testZebra() { testZebraWith(B); }
    @Test public void testQuinn() { testQuinnWith(B); }
}
