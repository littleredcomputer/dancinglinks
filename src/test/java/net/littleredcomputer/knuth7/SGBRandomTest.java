package net.littleredcomputer.knuth7;

import org.junit.Test;

import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertThat;

public class SGBRandomTest {

    @Test
    public void nextRand() {
        // DEK provides this test in gb_flip.w in the Stanford GraphBase
        SGBRandom R = new SGBRandom(-314159);
        assertThat(R.nextRand(), is(119318998));
        for (int j = 1; j <= 133; j++) R.nextRand();
        assertThat(R.unifRand(0x55555555), is(748103812));
    }
}