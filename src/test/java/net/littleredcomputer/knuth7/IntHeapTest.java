package net.littleredcomputer.knuth7;

import org.junit.Test;

import java.util.Arrays;
import java.util.stream.IntStream;

import static java.util.stream.Collectors.toList;
import static org.hamcrest.Matchers.*;
import static org.junit.Assert.assertThat;

public class IntHeapTest {

    @Test
    public void heapify() {
        int[] a = {3,7,6,2,3,4,5,1,3};
        IntHeap h = new IntHeap(a, a.length, (r,s) -> r-s);
        assertThat(IntStream.generate(h::get).limit(a.length).boxed().collect(toList()), contains(7,6,5,4,3,3,3,2,1));
        int[] b = {3,7,6,2,3,4,5,1,3};
        IntHeap g = new IntHeap(b, b.length, (r,s) -> s-r);
        assertThat(IntStream.generate(g::get).limit(a.length).boxed().collect(toList()), contains(1,2,3,3,3,4,5,6,7));
        int[] c = {10,4,5,20,6,8,7,30};
        IntHeap k = new IntHeap(c, c.length, (r,s) -> r-s);
        k.get(); k.get(); k.get();
        assertThat(Arrays.stream(c, 0, c.length-3).boxed().collect(toList()), everyItem(both(greaterThan(0)).and(lessThan(10))));
        assertThat(Arrays.stream(c, c.length-3, c.length).boxed().collect(toList()), everyItem(both(greaterThanOrEqualTo(10)).and(lessThan(100))));

    }

    @Test
    public void randomTests() {
        SGBRandom R = new SGBRandom(-271828);
        for (int t = 0; t < 100; ++t) {
            int len = R.unifRand(100) + 2;
            int[] A = new int[len];
            Arrays.setAll(A, i -> R.unifRand(100));
            int cutoff = 1+R.unifRand(len-1);
            final boolean up = (t & 1) == 1;
            IntHeap h = new IntHeap(A, A.length, up ? Integer::compare : (r,s) -> Integer.compare(s,r));
            for (int k = 0; k < cutoff; ++k) h.get();
            if (up) {
                // We've generated a random array, heapified it, and then drawn off the
                // top member cutoff times. Each time, the extracted value has been put
                // at the end of the array. At this point, every element to the left of
                // the cutoff point should be <= every element to the right.
                int maxLeft = Arrays.stream(A, 0, A.length - cutoff).max().orElseThrow(IllegalStateException::new);
                int minRight = Arrays.stream(A, A.length - cutoff, A.length).min().orElseThrow(IllegalStateException::new);
                assertThat(maxLeft, lessThanOrEqualTo(minRight));
            } else {
                int minLeft = Arrays.stream(A, 0, A.length - cutoff).min().orElseThrow(IllegalStateException::new);
                int maxRight = Arrays.stream(A, A.length - cutoff, A.length).max().orElseThrow(IllegalStateException::new);
                assertThat(minLeft, greaterThanOrEqualTo(maxRight));
            }
        }
    }
}