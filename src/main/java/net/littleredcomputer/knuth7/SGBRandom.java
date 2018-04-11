package net.littleredcomputer.knuth7;

import com.google.common.primitives.UnsignedInts;

/**
 * The random number generator from the Stanford GraphBase
 */
public class SGBRandom {
    private static final int two_to_the_31 = 0x80000000;
    private final int[] A = new int[56];
    private int gb_fptr = 0;

    /* difference mod 2^31 */
    private int mod_diff(int x, int y) { return (x-y) & 0x7fffffff; }

    /**
     *  A random number generator bit-compatible with that provided by gb_flip.h in the
     *  Stanford GraphBase.
     *  @param seed used to initialize the RNG. The seed gives predictable results; there
     *              is no other influence on the random numbers produced.
     */
    public SGBRandom(int seed) {
        A[0] = -1;
        int prev = seed, next = 1;
        seed = prev = mod_diff(prev, 0);
        A[55] = prev;
        for (int i = 21; i != 0; i = (i+21)%55) {
            A[i] = next;
            // Compute a new next value, based on next, prev, and seed.
            next = mod_diff(prev, next);
            if ((seed & 1) != 0) seed = 0x40000000+(seed>>1);
            else seed >>= 1;
            next = mod_diff(next, seed);
            prev = A[i];
        }
        // Get the array values "warmed up"
        for (int i = 0; i < 5; ++i) gb_flip_cycle();
    }

    public int nextRand() {
        return A[gb_fptr] >= 0 ? A[gb_fptr--] : gb_flip_cycle();
    }

    public int unifRand(int m) {
        int t = two_to_the_31 - UnsignedInts.remainder(two_to_the_31, m);
        int r;
        do r = nextRand(); while (UnsignedInts.compare(t, r) <= 0);
        return r % m;
    }

    private int gb_flip_cycle() {
        int i, j;
        for (i = 1, j = 32; j <= 55; i++, j++) A[i] = mod_diff(A[i], A[j]);
        for (j = 1; i <= 55; i++, j++) A[i] = mod_diff(A[i], A[j]);
        gb_fptr = 54;
        return A[55];
    }
}
