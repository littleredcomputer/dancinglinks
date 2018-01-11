package net.littleredcomputer.dlx;

import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;
import org.junit.Test;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.*;

public class ExactCoverProblemTest {

    private Stream<Set<String>> allSolutionOptions(ExactCoverProblem p) {
        Joiner j = Joiner.on(' ');
        return p.allSolutions().stream().map(sol -> sol.stream().map(p::optionIndexToItemNames).map(j::join).collect(Collectors.toSet()));
    }

    @Test
    public void example5() {
        ExactCoverProblem p = ExactCoverProblem.parseFrom("a b c d e f g\nc e\na d g\nb c f\na d f\nb g\nd e g");
        assertThat(p.allSolutions(), is(Collections.singletonList(Arrays.asList(3, 4, 0))));
    }

    private String langfordPairsInstance(int n) {
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
        assertThat(p.allSolutions().stream().map(Sets::newTreeSet).collect(Collectors.toList()),
                is(Arrays.asList(ImmutableSet.of(1, 6, 7), ImmutableSet.of(2, 4, 8))));
    }

    @Test
    public void langfordPairs4() {
        ExactCoverProblem p = ExactCoverProblem.parseFrom(langfordPairsInstance(4));
        List<Set<Integer>> r = p.allSolutions().stream().map(Sets::newTreeSet).collect(Collectors.toList());
        assertThat(r, is(Arrays.asList(ImmutableSet.of(1, 10, 13, 15), ImmutableSet.of(4, 6, 12, 17))));
        assertThat(allSolutionOptions(ExactCoverProblem.parseFrom(langfordPairsInstance(4))).collect(Collectors.toList()), is(
                ImmutableList.of(
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
        List<Integer> counts = IntStream.range(2, 10)
                .map(i -> ExactCoverProblem.parseFrom(langfordPairsInstance(i)).allSolutions().size())
                .boxed()
                .collect(Collectors.toList());
        assertThat(counts, is(Arrays.asList(0, 2, 2, 0, 0, 52, 300, 0)));
    }

    private String nQueensWithSlackInstance(int n) {
        StringBuilder sb = new StringBuilder();
        IntStream.range(1, n + 1).forEach(i -> sb.append('r').append(i).append(' ').append('c').append(i).append(' '));
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
        // slack options
        IntStream.range(2, 2 * n + 1).forEach(i -> sb.append('a').append(i).append('\n'));
        IntStream.range(-n + 1, n).forEach(i -> sb.append('b').append(i).append('\n'));
        return sb.toString();
    }

    @Test
    public void fourQueensWithSlack() {
        // See (23) in [fasc5c]
        ExactCoverProblem p = ExactCoverProblem.parseFrom(nQueensWithSlackInstance(4));
        assertThat(allSolutionOptions(p).collect(Collectors.toList()), is(
                ImmutableList.of(
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
                        .mapToLong(i->ExactCoverProblem.parseFrom(nQueensWithSlackInstance(i)).allSolutions().size())
                        .toArray(),
                is(new long[] {2, 10, 4, 40, 92, 352, 724})
        );
    }
}
