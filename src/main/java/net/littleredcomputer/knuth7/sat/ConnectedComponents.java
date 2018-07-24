package net.littleredcomputer.knuth7.sat;

import java.util.List;

class ConnectedComponents {
    // An implementation of Tarjan's algorithm adapted to the problem of lookahead in a SAT solver
    // In particular, this has been designed to perform no heap allocations whatsoever, so that the
    // use of this object during SAT solving will not result in any increment in memory pressure.

    private SATAlgorithmL.Literal activeStack;
    private SATAlgorithmL.Literal settledStack;
    private int nn;

    SATAlgorithmL.Literal settled() { return settledStack; }

    void find(List<SATAlgorithmL.Literal> view) {
        for (int i = 0; i < view.size(); ++i) {
            final SATAlgorithmL.Literal l = view.get(i);
            l.rank = 0;
            l.untagged = 0;
        }
        activeStack = null;
        settledStack = null;
        nn = 0;
        for (int i = 0; i < view.size(); ++i) {
            if (view.get(i).rank == 0) process(view.get(i));
        }
    }

    private void makeActive(SATAlgorithmL.Literal v) {
        v.rank = ++nn;
        v.link = activeStack;
        activeStack = v;
        v.min = v;
    }

    private void process(SATAlgorithmL.Literal v) {
        v.parent = null;
        // Make vertex l active
        makeActive(v);
        do {
            // Explore one step from the current vertex v, possibly moving to another current vertex
            // and calling it v
            SATAlgorithmL.Literal u;

            if (v.untagged < v.arcs.size()) {
                u = v.arcs.get(v.untagged);  // u = the tip of the untagged arc from v
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

        for (; t != v; t = t.link) {
            t.rank = Integer.MAX_VALUE;  // now t is settled
            t.parent = v;  // and its strong component is represented by v
        }
        v.rank = Integer.MAX_VALUE;
        v.parent = v;
    }
}
