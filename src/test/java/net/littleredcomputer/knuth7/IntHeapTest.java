package net.littleredcomputer.knuth7;

import gnu.trove.list.array.TIntArrayList;
import org.junit.Test;

import java.util.stream.IntStream;
import java.util.stream.Stream;

import static java.util.stream.Collectors.toList;
import static org.hamcrest.Matchers.*;
import static org.junit.Assert.assertThat;

public class IntHeapTest {

    @Test
    public void heapify() {
        final int[] ints = new int[]{3,7,6,2,3,4,5,1,3};
        TIntArrayList a = new TIntArrayList(ints);
        IntHeap h = new IntHeap(a, (r,s) -> r-s);
        h.heapify();
        assertThat(IntStream.generate(h::pop).limit(a.size()).boxed().collect(toList()), contains(7,6,5,4,3,3,3,2,1));
        TIntArrayList b = new TIntArrayList(ints);
        IntHeap g = new IntHeap(b, (r,s) -> s-r);
        g.heapify();
        assertThat(IntStream.generate(g::pop).limit(b.size()).boxed().collect(toList()), contains(1,2,3,3,3,4,5,6,7));
        TIntArrayList c = new TIntArrayList(new int[]{10,4,5,20,6,8,7,30});
        IntHeap k = new IntHeap(c, (r,s) -> r-s);
        k.heapify();
        assertThat(k.pop(), is(30));
        assertThat(k.pop(), is(20));
        assertThat(k.pop(), is(10));
    }

    @Test
    public void randomTests() {
        SGBRandom R = new SGBRandom(-271828);
        for (int t = 0; t < 100; ++t) {
            int len = R.unifRand(100) + 2;
            TIntArrayList A = new TIntArrayList(len);
            for (int i = 0; i < len; ++i) A.add(R.unifRand(100));
            int cutoff = 1+R.unifRand(len-1);
            final boolean up = (t & 1) == 1;
            IntHeap h = new IntHeap(A, up ? Integer::compare : (r,s) -> Integer.compare(s,r));
            h.heapify();
            IntStream segment = IntStream.generate(h::pop).limit(cutoff);
            // m should be <= [resp. >=] every remaining element.
            if (up) {
                int m = segment.min().getAsInt();
                assertThat(m, is(greaterThanOrEqualTo(Stream.generate(h::pop).limit(len-cutoff).max(Integer::compare).get())));
            } else {
                int m = segment.max().getAsInt();
                assertThat(m, is(lessThanOrEqualTo(Stream.generate(h::pop).limit(len-cutoff).min(Integer::compare).get())));
            }
        }
    }
}
