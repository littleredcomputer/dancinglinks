package net.littleredcomputer.knuth7;

public class ConnectedComponents {
    // An implementation of Tarjan's algorithm adapted to the problem of lookahead in a SAT solver
    // In particular, we wish to avoid memory allocation, if possible.

    // What we need:
    // A collection of vertices, and for each of them, a collection of edges, that we can partition
    // into tagged and untagged.

    // The desire to avoid allocation poses a challenge here. Essentially, the vertices are literals,
    // and so we would like to reuse the data already allocated to the literals in the computation of
    // the connected components.

    final SATAlgorithmL.Literal[] vertices;
    private SATAlgorithmL.Literal activeStack = null;
    private SATAlgorithmL.Literal settledStack = null;
    private int nn = 0;

    public ConnectedComponents(SATAlgorithmL.Literal[] vertices, int nVertices) {
        this.vertices = vertices;

        for (int i = 0; i < vertices.length; ++i) {
            vertices[i].rank = 0;
            vertices[i].untagged = 0;
        }
    }

    public void find() {
        for (int v = 0; v < vertices.length; ++v) {
            if (vertices[v].rank == 0) {
                process(vertices[v]);
            }
        }
    }

    private void makeActive(SATAlgorithmL.Literal v) {
        v.rank = ++nn;
        v.link = activeStack;
        activeStack = v;
        v.min = v;
    }

    public void process(SATAlgorithmL.Literal v) {
        SATAlgorithmL.Literal vv = v;
        v.parent = null;
        // Make vertex l active
        makeActive(v);
        do {
            // Explore one step from the current vertex v, possibly moving to another current vertex
            // and calling it v
            SATAlgorithmL.Literal u;

            if (v.untagged < v.BSIZE) {
                // XXX! if there are a subset of variables in the CAND array, isn't is also
                // probable that some of the entries in the BIMP table will not correspond
                // to a candidate variable? We will have to sift them more carefully.
                u = vertices[v.BIMP.getQuick(v.untagged)];  // u = the tip of the untagged arc from v
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
        System.out.printf("Strong component %d", v.id);
        if (t == v) System.out.println();
        else {
            System.out.println(" also includes:");
            for (; t != v; t = t.link) {
                System.out.printf("%d (from %d to %d)\n", t.id, t.parent.id, t.min.id);
                t.rank = Integer.MAX_VALUE;
                t.parent = v;
            }
        }
        v.rank = Integer.MAX_VALUE;
        v.parent = v;
    }
}
