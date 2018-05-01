package net.littleredcomputer.knuth7;

class ConnectedComponents {
    // An implementation of Tarjan's algorithm adapted to the problem of lookahead in a SAT solver
    // In particular, we wish to avoid memory allocation, if possible. (Still thinking about that.)

    // What we need:
    // A collection of vertices, and for each of them, a collection of edges, that we can partition
    // into tagged and untagged.

    // The desire to avoid allocation poses a challenge here. Essentially, the vertices are literals,
    // and so we would like to reuse the data already allocated to the literals in the computation of
    // the connected components.

    private final SATAlgorithmL.Literal[] vertices;

    private SATAlgorithmL.Literal activeStack = null;
    private SATAlgorithmL.Literal settledStack = null;
    private int nn = 0;

    ConnectedComponents(SATAlgorithmL.Literal[] vertices) {
        this.vertices = vertices;
    }

    SATAlgorithmL.Literal settled() { return settledStack; }

    void find(int[] view, int viewLength) {
        for (int i = 0; i < viewLength; ++i) {
            SATAlgorithmL.Literal l = vertices[view[i]];
            l.rank = 0;
            l.untagged = 0;
        }
        for (int i = 0; i < viewLength; ++i) {
            SATAlgorithmL.Literal l = vertices[view[i]];
            if (l.rank == 0) process(l);
        }
    }

    private void makeActive(SATAlgorithmL.Literal v) {
        v.rank = ++nn;
        v.link = activeStack;
        activeStack = v;
        v.min = v;
    }

    private void process(SATAlgorithmL.Literal v) {
        SATAlgorithmL.Literal vv = v;
        v.parent = null;
        // Make vertex l active
        makeActive(v);
        do {
            // Explore one step from the current vertex v, possibly moving to another current vertex
            // and calling it v
            SATAlgorithmL.Literal u;

            if (v.untagged < v.arcs.size()) {
                // XXX where we left off: this doesn't work. At some points, we need to
                // index over literals (from the cand array), but other times, we want data
                // from the literal table.
                u = vertices[v.arcs.getQuick(v.untagged)];  // u = the tip of the untagged arc from v
                ++v.untagged;
                if (u.rank != 0) {  // We've seen u already
                    if (u.rank < v.min.rank) v.min = u;  // non-tree arc, just update v.min
                } else {  // u is presently unseen
                    u.parent = v;  // the arc from v to u is a new tree arc
                    v = u;  // u will now be the current vertex
                    makeActive(v);
                }
            } else {  // all arcs from v are tagged, so v matures
                u = v.parent;
                if (v.min == v) {
                    announceComponent(v);
                } else {
                    // The arc from u to v has just matured, making v.min visible from u
                    if (v.min.rank < u.min.rank) u.min = v.min;
                }
                v = u;  // The former parent of v is the new current vertex v
            }
        } while (v != null);
    }

    private void announceComponent(SATAlgorithmL.Literal v) {
        // Remove v and all its successors on the active stack from the tree,
        // and mark them as a strong component of the graph
        SATAlgorithmL.Literal t;  // runs through the vertices of the new strong component
        t = activeStack;
        activeStack = v.link;
        v.link = settledStack;
        settledStack = t;  // We've moved the top of one stack to the other

        // System.out.println(" also includes:");
        for (; t != v; t = t.link) {
            // System.out.printf("%d (from %d to %d)\n", t.id, t.parent.id, t.min.id);
            t.rank = Integer.MAX_VALUE;  // now t is settled
            t.parent = v;  // and its strong component is represented by v
        }
        v.rank = Integer.MAX_VALUE;
        v.parent = v;
    }
}
