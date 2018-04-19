package net.littleredcomputer.knuth7;

import org.junit.Test;

import java.util.Arrays;
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
    private SATAlgorithmL.Literal[] createInstance(int n, int... arcs) {
        SATAlgorithmL.Literal[] v = new SATAlgorithmL.Literal[n];
        Arrays.setAll(v, SATAlgorithmL.Literal::new);
        for (int i = 0; i < arcs.length; i += 2) {
            v[arcs[i]].BIMP.add(arcs[i+1]);
            ++v[arcs[i]].BSIZE;
        }
        return v;
    }

    @Test
    public void ex1() {
        SATAlgorithmL.Literal[] v = createInstance(5, 0,2, 0,3, 1,0, 2,1, 3,4);
        ConnectedComponents cc = new ConnectedComponents(v, v.length);
        cc.find();
    }

    @Test
    public void ex2() {
        SATAlgorithmL.Literal[] v = createInstance(4, 0,1, 1,2, 2,3);
        ConnectedComponents cc = new ConnectedComponents(v, v.length);
        cc.find();
    }

    @Test
    public void ex3() {
        SATAlgorithmL.Literal[] v = createInstance(7, 0,1, 1,2, 2,0, 1,3, 1,4, 1,6, 3,5, 4,5);
        ConnectedComponents cc = new ConnectedComponents(v, v.length);
        cc.find();
    }

    @Test
    public void ex4() {
        SATAlgorithmL.Literal[] v = createInstance(11, 0,1, 0,3, 1,2, 1,4, 2,0, 2,6, 3,2, 4,5, 4,6, 5,6, 5,7, 5,8, 5,9, 6,4, 7,9, 8,9, 9,8);
        ConnectedComponents cc = new ConnectedComponents(v, v.length);
        cc.find();
        //noinspection unchecked
        assertThat(Arrays.stream(v).collect(Collectors.toMap(x -> x.id, x -> x.parent.id)),
                allOf(hasEntry(0, 0), hasEntry(1, 0), hasEntry(2, 0), hasEntry(3, 0),
                        hasEntry(4, 6), hasEntry(5, 6), hasEntry(6, 6),
                        hasEntry(7, 7),
                        hasEntry(8, 9), hasEntry(9, 9),
                        hasEntry(10, 10)));
    }

    @Test
    public void ex5() {
        SATAlgorithmL.Literal[] v = createInstance(5, 0,1, 1,2, 2,3, 2,4, 3,0, 4,2);
        ConnectedComponents cc = new ConnectedComponents(v, v.length);
        cc.find();
        assertThat(Arrays.stream(v).mapToInt(x -> x.parent.id).allMatch(i -> i == 0), is(true));
    }
}