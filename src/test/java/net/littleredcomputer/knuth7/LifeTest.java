package net.littleredcomputer.knuth7;

import org.junit.Test;

import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.hamcrest.Matchers.*;
import static org.junit.Assert.assertThat;

public class LifeTest {
    private static Life block = Life.fromDots(".... .**. .**. ....");
    private static Life beehive = Life.fromDots("...... ..**.. .*..*. ..**.. ......");
    private static Life blinker0 = Life.fromDots("..... ..*.. ..*.. ..*.. .....");
    private static Life blinker1 = Life.fromDots("..... ..... .***. ..... .....");
    private static Life loaf = Life.fromDots("...... ..**.. .*..*. ..*.*. ...*.. ......");
    private static Life boat = Life.fromDots("..... .**.. .*.*. ..*.. .....");
    private static Life tub = Life.fromDots("..... ..*.. .*.*. ..*.. .....");
    private static Life toad0 = Life.fromDots("...... ...*.. .*..*. .*..*. ..*... ......");
    private static Life toad1 = Life.fromDots("...... ...... ..***. .***.. ...... ......");
    private static Life beacon0 = Life.fromDots("...... .**... .*.... ....*. ...**. ......");
    private static Life beacon1 = Life.fromDots("...... .**... .**... ...**. ...**. ......");
    private static Life cross = Life.fromDots(
            ".......... " +
                    "...****... " +
                    "...*..*... " +
                    ".***..***. " +
                    ".*......*. " +
                    ".*......*. " +
                    ".***..***. " +
                    "...*..*... " +
                    "...****... " +
                    ".......... ");

    @Test public void blockIsStationary() { assertThat(block.step(), is(block)); }
    @Test public void beehiveIsStationary() { assertThat(beehive.step(), is(beehive)); }
    @Test public void loafIsStationary() { assertThat(loaf.step(), is(loaf)); }
    @Test public void boatIsStationary() { assertThat(boat.step(), is(boat)); }
    @Test public void tubIsStationary() { assertThat(tub.step(), is(tub)); }
    @Test public void blinkersAlternate() {
        assertThat(blinker0.step(), is(blinker1));
        assertThat(blinker1.step(), is(blinker0));
    }
    @Test public void toadsAlternate() {
        assertThat(toad0, is(not(toad1)));
        assertThat(toad0.step(), is(toad1));
        assertThat(toad1.step(), is(toad0));
    }
    @Test public void beaconsAlternate() {
        assertThat(beacon0, is(not(beacon1)));
        assertThat(beacon0.step(), is(beacon1));
        assertThat(beacon1.step(), is(beacon0));
    }
    @Test public void crossHasPeriod3() {
        assertThat(Stream.iterate(cross, Life::step)
                        .limit(4)
                        .map(x -> x.equals(cross))
                        .collect(Collectors.toList()),
                contains(true, false, false, true));
    }
}