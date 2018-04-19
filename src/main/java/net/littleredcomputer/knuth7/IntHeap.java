package net.littleredcomputer.knuth7;

import java.util.function.IntBinaryOperator;

public class IntHeap {
    private final int[] a;
    private final IntBinaryOperator compare;
    private int n;

    IntHeap(int[] a, int n, IntBinaryOperator compare) {
        this.a = a;
        this.n = n;
        this.compare = compare;
        heapify();
    }

    public void heapify() {
        int start = (n - 2) / 2;
        while (start >= 0) {
            siftDown(a, start, n-1);
            --start;
        }
    }

    private void siftDown(int[] A, int start, int end) {
        int root = start, child;
        while ((child = 2*root+1) <= end) {
            int swap = root;
            if (compare.applyAsInt( A[swap], A[child]) < 0) swap = child;
            if (child+1 <= end && compare.applyAsInt(A[swap], A[child+1]) < 0) swap = child+1;
            if (swap == root) return;
            int tmp = A[root];
            A[root] = A[swap];
            A[swap] = tmp;
            root = swap;
        }
    }

    public int get() {
        int top = a[0];
        --n;
        a[0] = a[n];
        a[n] = top;
        siftDown(a, 0, n-1);
        return top;
    }
}
