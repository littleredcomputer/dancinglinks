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

public class ProblemTest {

    private List<List<Integer>> results(Problem p) {
        List<List<Integer>> results = new ArrayList<>();

        p.onSolution((s) -> {
            results.add(s);
            return true;
        });
        p.solve();
        return results;
    }

    @Test
    public void example5() {
        Problem p = new Problem();
        p.parse("a b c d e f g\nc e\na d g\nb c f\na d f\nb g\nd e g");
        List<List<Integer>> r = results(p);
        assertThat(r, is(Collections.singletonList(Arrays.asList(3, 4, 0))));
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
        Problem p = new Problem().parse(langfordPairsInstance(3));
        assertThat(results(p), is(Arrays.asList(Arrays.asList(1, 7, 6), Arrays.asList(2, 4, 8))));
    }

    @Test
    public void langfordPairs4() {
        Problem p = new Problem().parse(langfordPairsInstance(4));
        List<List<Integer>> r = results(p);
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
                .map(i -> results(new Problem().parse(langfordPairsInstance(i))).size())
                .boxed()
                .collect(Collectors.toList());
        assertThat(counts, is(Arrays.asList(0, 2, 2, 0, 0, 52, 300, 0)));
    }
}
