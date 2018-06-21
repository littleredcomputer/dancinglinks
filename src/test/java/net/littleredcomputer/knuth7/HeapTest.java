package net.littleredcomputer.knuth7;

import org.junit.Test;

import java.util.Arrays;
import java.util.stream.Stream;

import static java.util.stream.Collectors.toList;
import static org.hamcrest.Matchers.*;
import static org.junit.Assert.assertThat;

public class HeapTest {

    static class BackwardInteger implements Comparable<BackwardInteger> {
        int i;
        BackwardInteger(int i) { this.i = i; }
        @Override public int compareTo(BackwardInteger o) { return o.i - i; }
    }

    @Test
    public void heapify() {
        Heap<Integer> h = new Heap<>();
        final int[] data = new int[]{3, 7, 6, 2, 3, 4, 5, 1,3};
        Integer[] ints = new Integer[data.length];
        for (int i = 0; i < ints.length; ++i) ints[i] = data[i];
        h.heapify(ints, ints.length);
        assertThat(Stream.generate(h::pop).limit(ints.length).collect(toList()), contains(7,6,5,4,3,3,3,2,1));
        Heap<BackwardInteger> g = new Heap<>();
        BackwardInteger[] bints = new BackwardInteger[ints.length];
        for (int i = 0; i < bints.length; ++i) bints[i] = new BackwardInteger(data[i]);
        g.heapify(bints, bints.length);
        assertThat(Stream.generate(g::pop).limit(bints.length).map(b -> b.i).collect(toList()), contains(1,2,3,3,3,4,5,6,7));
    }

    @Test
    public void randomTests() {
        SGBRandom R = new SGBRandom(-271828);
        Heap<Integer> h = new Heap<>();
        for (int t = 0; t < 100; ++t) {
            int len = R.unifRand(100) + 2;
            Integer[] A = new Integer[len];
            Arrays.setAll(A, i -> R.unifRand(100));
            int cutoff = 1+R.unifRand(len-1);
            h.heapify(A, A.length);
            Stream<Integer> segment = Stream.generate(h::pop).limit(cutoff);
            // m should be <= every remaining element.
            int m = segment.min(Integer::compare).get();
            assertThat(m, is(greaterThanOrEqualTo(Stream.generate(h::pop).limit(len-cutoff).max(Integer::compare).get())));
        }
    }
}
