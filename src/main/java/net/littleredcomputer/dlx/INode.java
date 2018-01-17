package net.littleredcomputer.dlx;

public class INode {
    INode(String name) {
        this.name = name;
    }
    int llink, rlink;
    final String name;
}
