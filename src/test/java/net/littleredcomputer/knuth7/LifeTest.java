package net.littleredcomputer.knuth7;

import org.junit.Test;

import java.util.Optional;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static com.github.npathai.hamcrestopt.OptionalMatchers.isPresent;
import static com.github.npathai.hamcrestopt.OptionalMatchers.isPresentAndIs;
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
        assertThat(blinker0, is(not(blinker1)));
        assertThat(blinker0.step(), is(blinker1));
        assertThat(blinker1.step(), is(blinker0));
    }
    @Test public void toadsAlternate() {
        assertThat(Stream.iterate(toad0, Life::step)
                .limit(4)
                .collect(Collectors.toList()),
                contains(toad0, toad1, toad0, toad1));
    }
    @Test public void beaconsAlternate() {
        assertThat(Stream.iterate(beacon0, Life::step)
                        .limit(4)
                        .collect(Collectors.toList()),
                contains(beacon0, beacon1, beacon0, beacon1));
    }
    @Test public void crossHasPeriod3() {
        assertThat(Stream.iterate(cross, Life::step)
                        .limit(7)
                        .map(x -> x.equals(cross))
                        .collect(Collectors.toList()),
                contains(true, false, false, true, false, false, true));
    }
    @Test public void ancestor1() {
        Life l = Life.fromDots("..... .*.*. ..*.. .*.*. .....");
        assertThat(new SATAlgorithmD(l.ancestor())
                .solve()
                .map(s -> Life.fromSolution(l.r, l.c, s))
                .map(Life::step), isPresentAndIs(l));
    }
    @Test public void ancestorOneLine() {
        Life l = Life.fromDots("...***...");
        assertThat(new SATAlgorithmD(l.ancestor())
                .solve()
                .map(s -> Life.fromSolution(l.r, l.c, s))
                .map(Life::step), isPresentAndIs(l));
    }
    @Test public void ancestorOneColumn() {
        Life l = Life.fromDots(". . . * * * . . .");
        assertThat(new SATAlgorithmD(l.ancestor())
                .solve()
                .map(s -> Life.fromSolution(l.r, l.c, s))
                .map(Life::step), isPresentAndIs(l));
    }

    /**
     * Do the following N times:
     *   * create a random r x c Life grid L (where each cell has a 50% chance to be populated)
     *   * step it forward to get Lʹ
     *   * create the SAT problem corresponding to the ancestors of Lʹ
     *   * solve it (it has a solution because we generated the tableau via step)
     *   * ensure that the step of the solution results in Lʹ.
     * It need not be true that the solution is the same as L. A life tableau may have several
     * ancestors.
     */
    private void testRandomGridAncestor(Function<SATProblem, AbstractSATSolver> solver, int N, int r, int c) {
        SGBRandom rng = new SGBRandom(314159);
        for (int t = 0; t < N; ++t) {
            Life l0 = new Life(r, c);
            // We generate a random tableau, and step it: this results in a tableau that has at least
            // one ancestor, so we know the corresponding SAT instance will be solvable.
            for (int i = 0; i < r; ++i) for (int j = 0; j < c; ++j) l0.x[i][j] = rng.unifRand(2) > 0;
            Life l = l0.step();
            Optional<Life> sol = solver.apply(l.ancestor()).solve().map(s -> Life.fromSolution(r, c, s));
             //System.out.printf("original %s\n step %s\n ancestor %s\n", l0, l, sol);
            assertThat(sol, isPresent());
            sol.ifPresent(a -> assertThat(a.step(), is(l)));
        }
    }

    @Test public void random7x7A() { testRandomGridAncestor(SATAlgorithmA::new, 20, 7, 7); }
    @Test public void random6x6A() { testRandomGridAncestor(SATAlgorithmA::new, 20, 6, 6); }
    @Test public void random7x7B() { testRandomGridAncestor(SATAlgorithmB::new, 20, 7, 7); }
    @Test public void random6x6B() { testRandomGridAncestor(SATAlgorithmB::new, 20, 6, 6); }
    @Test public void random7x7D() { testRandomGridAncestor(SATAlgorithmD::new, 20, 7, 7); }
    @Test public void random6x6D() { testRandomGridAncestor(SATAlgorithmD::new, 20, 6, 6); }


    // These are too hard for L3 at the moment.
    // @Test public void random7x7L3() { testRandomGridAncestor(p -> new SATAlgorithmL(p.to3SAT()), 20, 7, 7); }
    // @Test public void random6x6L3() { testRandomGridAncestor(p -> new SATAlgorithmL(p.to3SAT()), 20, 6, 6); }

    /* @Test */ public void testGrid() {
        Life l = Life.fromDots(
            "...................... " +
            "............*.*....... " +
            "..***..***..*...*.**.. " +
            ".*....*...*.*.*.**..*. " +
            ".*....*...*.*.*.*...*. " +
            "..***..***..*.*.*...*. " +
            "...................... ");
        Optional<boolean[]> solution = new SATAlgorithmD(l.ancestor()).solve();
        solution.ifPresent(s -> System.out.println(Life.fromSolution(l.r, l.c, s)));
    }

    /* @Test */ public void testGrid2() {
        Life l = Life.fromDots(".............*........ " +
                "..***..*.**....*.***.. " +
                ".*...*.**..*.*.**...*. " +
                ".*****.*.....*.*....*. " +
                ".*.....*.....*.*....*. " +
                "..***..*.....*.*....*. ");
        for (int i = 1; i < 4; ++i) {
            Optional<boolean[]> solution = new SATAlgorithmD(l.ancestor()).solve();
            if (!solution.isPresent()) {
                System.out.println("unsat :(");
                break;
            }
            l = Life.fromSolution(l.r, l.c, solution.get());
            System.out.printf("STEP %d\n", i);
            System.out.println(l);
        }
    }

    @Test public void testGrid3() {
        Life l = Life.fromDots(
                "........ " +
                "..*..*.. " +
                "........ " +
                ".*....*. " +
                "..****.. " +
                "........ ");
        for (int i = 1; i < 4; ++i) {
            Optional<boolean[]> solution = new SATAlgorithmD(l.ancestor()).solve();
            if (!solution.isPresent()) {
                System.out.println("unsat :(");
                break;
            }
            l = Life.fromSolution(l.r, l.c, solution.get());
            System.out.printf("STEP %d\n", i);
            System.out.println(l);
        }
    }

}