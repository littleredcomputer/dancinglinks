import com.google.common.collect.ImmutableList;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.*;

public class ExactCoverProblemTest {

    @Test
    public void example5() {
        ExactCoverProblem p = new ExactCoverProblem();
        p.parse("a b c d e f g\nc e\na d g\nb c f\na d f\nb g\nd e g");
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
        ExactCoverProblem p = new ExactCoverProblem().parse(langfordPairsInstance(3));
        assertThat(p.allSolutions(), is(Arrays.asList(Arrays.asList(1, 7, 6), Arrays.asList(2, 4, 8))));
    }

    @Test
    public void langfordPairs4() {
        ExactCoverProblem p = new ExactCoverProblem().parse(langfordPairsInstance(4));
        List<List<Integer>> r = p.allSolutions();
        assertThat(r, is(Arrays.asList(Arrays.asList(1, 15, 10, 13), Arrays.asList(4, 6, 12, 17))));
        Stream<List<List<String>>> solutions = r.stream().map(sol ->
                sol.stream().map(p::optionIndexToItemNames).collect(Collectors.toList()));
        assertThat(solutions.collect(Collectors.toList()), is(
                ImmutableList.of(
                        ImmutableList.of(
                                ImmutableList.of("1", "s2", "s4"),
                                ImmutableList.of("s1", "s6", "4"),
                                ImmutableList.of("s5", "2", "s8"),
                                ImmutableList.of("3", "s3", "s7")),
                        ImmutableList.of(
                                ImmutableList.of("1", "s5", "s7"),
                                ImmutableList.of("s1", "2", "s4"),
                                ImmutableList.of("s2", "s6", "3"),
                                ImmutableList.of("s3", "4", "s8")))));
    }

    @Test
    public void langfordCounts() {
        List<Integer> counts = IntStream.range(2, 10)
                .map(i -> new ExactCoverProblem().parse(langfordPairsInstance(i)).allSolutions().size())
                .boxed()
                .collect(Collectors.toList());
        assertThat(counts, is(Arrays.asList(0, 2, 2, 0, 0, 52, 300, 0)));
    }
}
