package net.littleredcomputer.dlx;

import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
// Copyright 2018 Colin Smith. MIT License.
import com.google.common.collect.Sets;
import org.junit.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertThat;

public class ExactCoverProblemTest {

    private List<Set<String>> allSolutionOptions(ExactCoverProblem p) {
        Joiner j = Joiner.on(' ');
        return p.solutions()
                .map(p::optionsToItems)
                .map(s -> s.stream().map(j::join).collect(Collectors.toSet()))
                .collect(Collectors.toList());
    }

    @Test(expected = IllegalArgumentException.class)
    public void mustHaveAtLeastOnePrimaryOption() {
        ExactCoverProblem.parseFrom("; b c d\nb\nc\nd");
    }

    @Test(expected = IllegalArgumentException.class)
    public void cannotHaveTertiaryItems() {
        ExactCoverProblem.parseFrom("a ; b ; c\na\nb\nc");
    }

    @Test(expected = IllegalArgumentException.class)
    public void cannotRepeatItems() {
        ExactCoverProblem.parseFrom("a b a\na\nb");
    }

    @Test(expected = IllegalArgumentException.class)
    public void unknownItemInOption() {
        ExactCoverProblem.parseFrom("a b c\na\nd\nb");
    }

    @Test
    public void simple() {
        assertThat(ExactCoverProblem.parseFrom("a b c\na b\nb c\nc a\na").solutions().collect(Collectors.toList()),
                is(Collections.singletonList(Arrays.asList(1, 3))));
    }

    @Test
    public void example5() {
        ExactCoverProblem p = ExactCoverProblem.parseFrom("a b c d e f g\nc e\na d g\nb c f\na d f\nb g\nd e g");
        assertThat(p.solutions().collect(Collectors.toList()),
                is(Collections.singletonList(Arrays.asList(3, 4, 0))));
    }

    private String langfordPairsInstance(long n) {
        StringBuilder p = new StringBuilder();
        for (int i = 1; i <= n; ++i) {
            p.append(i).append(' ').append("s").append(i).append(' ').append("s").append(i + n).append(' ');
        }
        p.append('\n');

        for (int i = 1; i <= n; ++i) {
            int step = i + 1;
            for (int j = 1; j + step <= 2 * n; ++j) {
                p.append(i).append(' ').append("s").append(j).append(" s").append(j + step).append('\n');
            }
        }
        return p.toString();
    }

    @Test
    public void langfordPairs3() {
        ExactCoverProblem p = ExactCoverProblem.parseFrom(langfordPairsInstance(3));
        assertThat(p.solutions().map(Sets::newTreeSet).collect(Collectors.toList()),
                is(Arrays.asList(ImmutableSet.of(1, 6, 7), ImmutableSet.of(2, 4, 8))));
    }

    @Test
    public void langfordPairs4() {
        ExactCoverProblem p = ExactCoverProblem.parseFrom(langfordPairsInstance(4));
        List<Set<Integer>> r = p.solutions().map(Sets::newTreeSet).collect(Collectors.toList());
        assertThat(r, is(Arrays.asList(ImmutableSet.of(1, 10, 13, 15), ImmutableSet.of(4, 6, 12, 17))));
        assertThat(allSolutionOptions(ExactCoverProblem.parseFrom(langfordPairsInstance(4))), is(ImmutableList.of(
                ImmutableSet.of(
                        "1 s2 s4",
                        "4 s1 s6",
                        "2 s5 s8",
                        "3 s3 s7"),
                ImmutableSet.of(
                        "1 s5 s7",
                        "2 s1 s4",
                        "3 s2 s6",
                        "4 s3 s8"))));
    }

    @Test
    public void langfordCounts() {
        assertThat(IntStream.range(2, 10)
                        .mapToLong(i -> ExactCoverProblem.parseFrom(langfordPairsInstance(i)).solutions().count())
                        .toArray(),
                is(new long[]{0, 2, 2, 0, 0, 52, 300, 0}));
    }

    private String nQueensInstance(int n, boolean slack) {
        StringBuilder sb = new StringBuilder();
        IntStream.range(1, n + 1).forEach(i -> sb.append('r').append(i).append(' ').append('c').append(i).append(' '));
        if (!slack) {
            // If we aren't using slack items, then the diagonal items are secondary
            sb.append("; ");
        }
        IntStream.range(2, 2 * n + 1).forEach(i -> sb.append('a').append(i).append(' '));
        IntStream.range(-n + 1, n).forEach(i -> sb.append('b').append(i).append(' '));
        sb.append('\n');  // now for the options
        for (int i = 1; i <= n; ++i) {
            for (int j = 1; j <= n; ++j) {
                sb.append("r").append(i).append(' ').append("c").append(j).append(' ');
                sb.append("a").append(i + j).append(' ');
                sb.append("b").append(i - j).append('\n');
            }
        }
        if (slack) {
            // If using slack items, then we need corresponding slack options.
            IntStream.range(2, 2 * n + 1).forEach(i -> sb.append('a').append(i).append('\n'));
            IntStream.range(-n + 1, n).forEach(i -> sb.append('b').append(i).append('\n'));
        }
        return sb.toString();
    }

    @Test
    public void fourQueensWithSlack() {
        // See (23) in [fasc5c]
        ExactCoverProblem p = ExactCoverProblem.parseFrom(nQueensInstance(4, true));
        assertThat(allSolutionOptions(p), is(ImmutableList.of(
                ImmutableSet.of(
                        "a2",
                        "b3",
                        "r3 c1 a4 b2",
                        "r4 c3 a7 b1",
                        "a5",
                        "a8",
                        "b-3",
                        "b0",
                        "r1 c2 a3 b-1",
                        "r2 c4 a6 b-2"),
                ImmutableSet.of(
                        "a2",
                        "b3",
                        "r4 c2 a6 b2",
                        "a5",
                        "a8",
                        "b-3",
                        "r2 c1 a3 b1",
                        "r1 c3 a4 b-2",
                        "r3 c4 a7 b-1",
                        "b0"))));
    }


    @Test
    public void queensWithSlackCounts() {
        // Computes a table of Q(n) as given in [fasc5b 7.2.2], using the slack-variable version of the n-queens XC problem.
        // See also https://en.wikipedia.org/wiki/Eight_queens_puzzle#Counting_solutions
        assertThat(
                IntStream.range(4, 11)
                        .mapToLong(i -> ExactCoverProblem.parseFrom(nQueensInstance(i, true)).solutions().count())
                        .toArray(),
                is(new long[]{2, 10, 4, 40, 92, 352, 724})
        );
    }

    @Test
    public void fourQueensWithSecondaryItems() {
        // See (23) in [fasc5c]
        ExactCoverProblem p = ExactCoverProblem.parseFrom(nQueensInstance(4, false));
        assertThat(allSolutionOptions(p), is(ImmutableList.of(
                ImmutableSet.of(
                        "r3 c1 a4 b2",
                        "r4 c3 a7 b1",
                        "r1 c2 a3 b-1",
                        "r2 c4 a6 b-2"),
                ImmutableSet.of(
                        "r4 c2 a6 b2",
                        "r2 c1 a3 b1",
                        "r1 c3 a4 b-2",
                        "r3 c4 a7 b-1"))));
    }

    @Test
    public void queensWithSecondaryItemsCounts() {
        // Compute Q(n) using the secondary-items n-queens formulation
        assertThat(
                IntStream.range(4, 11)
                        .mapToLong(i -> ExactCoverProblem.parseFrom(nQueensInstance(i, false)).solutions().count())
                        .toArray(),
                is(new long[]{2, 10, 4, 40, 92, 352, 724})
        );
    }

    private char encode(int i) {
        if (i < 0 || i > 61) throw new IllegalArgumentException("out of range");
        if (i < 10) return (char) (0x30 + i);
        if (i < 36) return (char) (0x57 + i);
        return (char) (0x1d + i);
    }

    private void gridItems(StringBuilder sb, int m) {
        for (int x = 0; x < m; ++x) {
            for (int y = 0; y < m; ++y) {
                sb.append(encode(x)).append(encode(y)).append(' ');
            }
        }
    }

    /**
     * Options for a square n x n object to lie within an m x m grid.
     * We assume coordinates are of the form
     *
     * @param n side length of square object
     * @param m side length of square arena
     */
    private void squarePieceOptions(StringBuilder sb, String name, int n, int m) {
        for (int x = 0; x <= m - n; ++x) {
            for (int y = 0; y <= m - n; ++y) {
                sb.append(name).append(' ');
                for (int i = 0; i < n; ++i) {
                    for (int j = 0; j < n; ++j) {
                        sb.append(encode(x + i)).append(encode(y + j)).append(' ');
                    }
                }
                sb.append('\n');
            }
        }
    }

//    public void easySquarePackingProblem() {
//        StringBuilder items = new StringBuilder();
//        // Let's start with a small, solvable problem. Pack 1 1x1, 5 2x2, 3 3x3 and 3 4x4 cells
//        // into a 10x10 grid. That won't fill the whole grid so let all the cell options be secondary
//        // but require placement of all the pieces.
//        StringBuilder pd = new StringBuilder();
//        final int M = 10;
//        pd.append("p1.0 p2.0 p2.1 p2.2 p2.3 p2.4 p3.0 p3.1 p3.2 p4.0 p4.1 p4.2 ; ");
//        gridItems(pd, M);
//        pd.append('\n');
//        squarePieceOptions(pd, "p1.0", 1, M);
//        squarePieceOptions(pd, "p2.0", 2, M);
//        squarePieceOptions(pd, "p2.1", 2, M);
//        squarePieceOptions(pd, "p2.2", 2, M);
//        squarePieceOptions(pd, "p2.3", 2, M);
//        squarePieceOptions(pd, "p2.4", 2, M);
//        for (int i = 0; i < 3; ++i) {
//            squarePieceOptions(pd, "p3."+i, 3, M);
//            squarePieceOptions(pd, "p4."+i, 4, M);
//        }
//        ExactCoverProblem p = ExactCoverProblem.parseFrom(pd.toString());
//        p.solve(s -> {
//            System.out.println(s);
//            return true;
//        });
//
//    }
}
