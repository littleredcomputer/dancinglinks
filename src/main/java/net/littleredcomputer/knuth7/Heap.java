package net.littleredcomputer.knuth7;

class Heap<T extends Comparable<T>> {
    private T[] a;
    private int n;

    void heapify(T[] a, int n) {
        this.a = a;
        this.n = n;

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
            if (a[swap].compareTo(a[child]) < 0) swap = child;
            if (child+1 <= end && a[swap].compareTo(a[child+1]) < 0) swap = child+1;
            if (swap == root) return;
            T tmp = a[root];
            a[root] = a[swap];
            a[swap] = tmp;
            root = swap;
        }
    }

    T pop() {
        if (n < 1) throw new IllegalStateException("pop from empty heap");
        T top = a[0];
        a[0] = a[--n];
        siftDown(0, n-1);
        return top;
    }
}
