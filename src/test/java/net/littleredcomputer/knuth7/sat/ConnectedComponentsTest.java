package net.littleredcomputer.knuth7.sat;

import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import static org.hamcrest.Matchers.*;
import static org.junit.Assert.assertThat;

public class ConnectedComponentsTest {

    /**
     * Creates a graph instance suitable for input to ConnectedComponents.
     * @param n number of vertices
     * @param arcs taken pairwise, arcs between vertices (considered as a 0-based array)
     * @return array of vertices of length n containing arcs as specified.
     */
    private List<SATAlgorithmL.Literal> createVertexArray(int n, int... arcs) {
        List<SATAlgorithmL.Literal> v = new ArrayList<>(n);
        for (int i = 0; i < n; ++i) v.add(new SATAlgorithmL.Literal(i));
        for (int i = 0; i < arcs.length; i += 2) {
            v.get(arcs[i]).arcs.add(v.get(arcs[i+1]));
        }
        return v;
    }

    @Test
    public void ex1() {
        List<SATAlgorithmL.Literal> vs = createVertexArray(5, 0,2, 0,3, 1,0, 2,1, 3,4);
        new ConnectedComponents().find(vs);
    }

    @Test
    public void ex2() {
        List<SATAlgorithmL.Literal> vs = createVertexArray(4, 0,1, 1,2, 2,3);
        new ConnectedComponents().find(vs);
    }

    @Test
    public void ex3() {
        List<SATAlgorithmL.Literal> vs = createVertexArray(7, 0,1, 1,2, 2,0, 1,3, 1,4, 1,6, 3,5, 4,5);
        new ConnectedComponents().find(vs);
    }

    @Test
    public void ex4() {
        List<SATAlgorithmL.Literal> vs = createVertexArray(11, 0,1, 0,3, 1,2, 1,4, 2,0, 2,6, 3,2, 4,5, 4,6, 5,6, 5,7, 5,8, 5,9, 6,4, 7,9, 8,9, 9,8);
        new ConnectedComponents().find(vs);
        //noinspection unchecked
        assertThat(vs.stream().collect(Collectors.toMap(x -> x.id, x -> x.parent.id)),
                allOf(hasEntry(0, 0), hasEntry(1, 0), hasEntry(2, 0), hasEntry(3, 0),
                        hasEntry(4, 6), hasEntry(5, 6), hasEntry(6, 6),
                        hasEntry(7, 7),
                        hasEntry(8, 9), hasEntry(9, 9),
                        hasEntry(10, 10)));
    }

    @Test
    public void ex4WithView() {
        List<SATAlgorithmL.Literal> vs = createVertexArray(11, 0,1, 0,3, 1,2, 1,4, 2,0, 2,6, 3,2, 4,5, 4,6, 5,6, 5,7, 5,8, 5,9, 6,4, 7,9, 8,9, 9,8);
        List<SATAlgorithmL.Literal> view = Arrays.asList(vs.get(2), vs.get(3), vs.get(4), vs.get(5));
        new ConnectedComponents().find(view);
        //noinspection unchecked
        assertThat(view.stream().collect(Collectors.toMap(x -> x.id, x -> x.parent.id)),
                allOf(hasEntry(2, 2), hasEntry(3, 2), hasEntry(4, 4), hasEntry(5, 4)));
    }

    @Test
    public void ex5() {
        List<SATAlgorithmL.Literal> vs = createVertexArray(5, 0,1, 1,2, 2,3, 2,4, 3,0, 4,2);
        new ConnectedComponents().find(vs);
        assertThat(vs.stream().mapToInt(x -> x.parent.id).allMatch(i -> i == 0), is(true));
    }
}
