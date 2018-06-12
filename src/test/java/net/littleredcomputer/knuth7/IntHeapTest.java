package net.littleredcomputer.knuth7;

import org.junit.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import static java.util.stream.Collectors.toList;
import static org.hamcrest.Matchers.*;
import static org.junit.Assert.assertThat;

public class IntHeapTest {

    static class BackwardInteger implements Comparable<BackwardInteger> {
        int i;
        BackwardInteger(int i) { this.i = i; }
        @Override public int compareTo(BackwardInteger o) { return o.i - i; }
    }

    @Test
    public void heapify() {
        Heap<Integer> h = new Heap<>();
        ArrayList<Integer> ints = new ArrayList<>(Arrays.asList(3, 7, 6, 2, 3, 4, 5, 1,3));
        h.heapify(ints);
        assertThat(Stream.generate(h::pop).limit(ints.size()).collect(toList()), contains(7,6,5,4,3,3,3,2,1));
        assertThat(ints, empty());
        Heap<BackwardInteger> g = new Heap<>();
        ArrayList<BackwardInteger> bints  = IntStream.of(3, 7, 6, 2, 3, 4, 5, 1, 3).mapToObj(BackwardInteger::new).collect(Collectors.toCollection(ArrayList::new));
        g.heapify(bints);
        assertThat(Stream.generate(g::pop).limit(bints.size()).map(b -> b.i).collect(toList()), contains(1,2,3,3,3,4,5,6,7));
        assertThat(bints, empty());
    }

    @Test
    public void randomTests() {
        SGBRandom R = new SGBRandom(-271828);
        Heap<Integer> h = new Heap<>();
        for (int t = 0; t < 100; ++t) {
            int len = R.unifRand(100) + 2;
            ArrayList<Integer> A = new ArrayList<>(len);
            for (int i = 0; i < len; ++i) A.add(R.unifRand(100));
            int cutoff = 1+R.unifRand(len-1);
            h.heapify(A);
            Stream<Integer> segment = Stream.generate(h::pop).limit(cutoff);
            // m should be <= every remaining element.
            int m = segment.min(Integer::compare).get();
            assertThat(m, is(greaterThanOrEqualTo(Stream.generate(h::pop).limit(len-cutoff).max(Integer::compare).get())));
        }
    }
}
