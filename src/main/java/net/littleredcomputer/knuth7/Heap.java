package net.littleredcomputer.knuth7;

import java.util.ArrayList;

class Heap<T extends Comparable<T>> {
    private ArrayList<T> a;

    void heapify(ArrayList<T> a) {
        this.a = a;
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
            if (a.get(swap).compareTo(a.get(child)) < 0) swap = child;
            if (child+1 <= end && a.get(swap).compareTo(a.get(child+1)) < 0) swap = child+1;
            if (swap == root) return;
            T tmp = a.get(root);
            a.set(root, a.get(swap));
            a.set(swap, tmp);
            root = swap;
        }
    }

    T pop() {
        T top = a.get(0);
        if (a.size() > 1) {
            a.set(0, a.remove(a.size() - 1));
            siftDown(0, a.size() - 1);
        }
        else a.clear();
        return top;
    }
}
