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
    final int nVertices;


    public ConnectedComponents(SATAlgorithmL.Literal[] vertices, int nVertices) {
        this.vertices = vertices;
        this.nVertices = nVertices;

        for (SATAlgorithmL.Literal v : vertices) {


        }
    }



}
