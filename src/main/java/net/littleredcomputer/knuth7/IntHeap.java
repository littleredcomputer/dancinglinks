package net.littleredcomputer.knuth7;

import gnu.trove.list.array.TIntArrayList;

import java.util.function.IntBinaryOperator;

class IntHeap {
    private final TIntArrayList a;
    private final IntBinaryOperator compare;

    IntHeap(TIntArrayList a, IntBinaryOperator compare) {
        this.a = a;
        this.compare = compare;
    }

    void heapify() {
        final int n = a.size();
        int start = (n - 2) / 2;
        while (start >= 0) {
            siftDown(start, n-1);
            --start;
        }
    }

    private void siftDown(int start, int end) {
        int root = start, child;
        while ((child = 2*root+1) <= end) {
            int swap = root;
            if (compare.applyAsInt(a.get(swap), a.get(child)) < 0) swap = child;
            if (child+1 <= end && compare.applyAsInt(a.get(swap), a.get(child+1)) < 0) swap = child+1;
            if (swap == root) return;
            int tmp = a.get(root);
            a.set(root, a.get(swap));
            a.set(swap, tmp);
            root = swap;
        }
    }

    public int pop() {
        int top = a.get(0);
        if (a.size() > 1) {
            a.set(0, a.removeAt(a.size() - 1));
            siftDown(0, a.size() - 1);
        }
        else a.resetQuick();
        return top;
    }
}
