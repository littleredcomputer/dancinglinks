package net.littleredcomputer.dlx;

import com.google.common.base.Splitter;
import com.google.common.collect.Lists;

import java.io.Reader;
import java.io.StringReader;
import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;


/**
 * An implementation of Knuth's Dancing Links algorithm from pre-fascicle 5C
 * of TAOCP volume 4.
 */
public class ExactCoverProblem {
    private static final Splitter splitter = Splitter.on(' ').omitEmptyStrings();

    public enum Strategy {
        FIRST,
        MRV,
    }
    private Strategy strategy = Strategy.MRV;
    private enum State {
        ADDING_ITEMS,
        ADDING_OPTIONS,
        SOLVING,
        COMPLETE,
    }
    private State state = State.ADDING_ITEMS;

    private final Map<String, Integer> itemIndex = new HashMap<>();
    private final INode inode0 = new INode();
    private final ArrayList<INode> inodes = Lists.newArrayList(inode0);
    private final ArrayList<XNode> xnodes = new ArrayList<>();
    private final ArrayList<Integer> optionByNumber = new ArrayList<>();
    private int optionCount = 0;

    private ExactCoverProblem(Iterable<String> items) {
        int N1 = 0;
        boolean secondaryItems = false;
        for (String item: items) {
            if (item.equals(";")) {
                if (secondaryItems) throw new IllegalArgumentException("tertiary items are not supported");
                if (inodes.size() == 1) throw new IllegalArgumentException("there must be at least one primary item");
                N1 = inodes.size() - 1;
                secondaryItems = true;
                continue;
            }
            if (itemIndex.containsKey(item)) throw new IllegalArgumentException("duplicate item: " + item);
            INode i = new INode();
            int ix = inodes.size();
            inodes.add(i);
            itemIndex.put(item, ix);
            i.name = item;
            i.llink = ix - 1;
            inodes.get(ix-1).rlink = ix;
        }
        int N = inodes.size() - 1;
        if (N1 == 0) N1 = N;
        INode last = new INode();
        last.llink = N;
        inodes.add(last);
        inodes.get(N).rlink = N+1;
        inodes.get(N1+1).llink = N+1;
        inodes.get(N1+1).rlink = N1+1;
        inode0.llink = N1;
        inodes.get(N1).rlink = 0;
    }

    public List<String> optionIndexToItemNames(int oi) {
        List<String> items = new ArrayList<>();
        for (int ix = optionByNumber.get(oi); xnodes.get(ix).top > 0; ++ix) {
            items.add(inodes.get(xnodes.get(ix).top).name);
        }
        return items;
    }

    /**
     * Add an option (nonempty subset of established items). Empty options are
     * ignored. Repeated items in an option are ignored. Referring to an unknown
     * option will throw.
     * @param items sequence of item names
     */
    private void addOption(Iterable<String> items) {
        if (state == State.ADDING_ITEMS) {
            state = State.ADDING_OPTIONS;
            // Add first spacer
            xnodes.add(new XNode());
            for (int i = 1; i < inodes.size(); ++i) {
                XNode x = new XNode();
                int ix = xnodes.size();
                xnodes.add(x);
                x.ulink = x.dlink = ix;
                x.top = i;
            }
            // Add spacer after head nodes.
            xnodes.add(new XNode());
        }
        if (state != State.ADDING_OPTIONS) {
            throw new IllegalStateException("cannot add more options now");
        }
        XNode leftSpacer = xnodes.get(xnodes.size() - 1);
        XNode rightSpacer = new XNode();
        List<Integer> indices = StreamSupport.stream(items.spliterator(), false)
                .distinct()
                .map(itemIndex::get)
                .collect(Collectors.toList());
        if (indices.size() == 0) return;
        int ix = 0;
        for (int ixnode : indices) {
            XNode xHead = xnodes.get(ixnode);
            xHead.len++;
            XNode x = new XNode();
            ix = xnodes.size();
            x.ulink = xHead.ulink;
            xnodes.get(xHead.ulink).dlink = ix;
            x.dlink = ixnode;
            x.top = ixnode;
            xHead.ulink = ix;
            if (rightSpacer.ulink == 0) {
                // The first item in the new option. We take care of two small bookkeeping tasks:
                // ULINK(x) of a spacer is the adddress of the first node in the option before x
                rightSpacer.ulink = ix;
                // An index from option index to first net.littleredcomputer.dlx.XNode in the option
                optionByNumber.add(xnodes.size());
            }
            xnodes.add(x);
        }
        leftSpacer.dlink = ix;
        leftSpacer.top = -optionCount;
        xnodes.add(rightSpacer);
        ++optionCount;
    }

    private void hide(int p) {
        // System.out.printf("hide %d\n", p);
        int q = p + 1;
        while (q != p) {
            XNode xq = xnodes.get(q);
            int x = xq.top;
            int u = xq.ulink;
            int d = xq.dlink;
            if (x <= 0) {
                q = u;
            } else {
                xnodes.get(u).dlink = d;
                xnodes.get(d).ulink = u;
                xnodes.get(x).len--;
                ++q;
            }
        }
    }

    private void cover(int i) {
        // System.out.printf("cover %d\n", i);
        int p = xnodes.get(i).dlink;
        while (p != i) {
            hide(p);
            p = xnodes.get(p).dlink;
        }
        INode ii = inodes.get(i);
        int l = ii.llink;
        int r = ii.rlink;
        inodes.get(l).rlink = r;
        inodes.get(r).llink = l;
    }

    private void uncover(int i) {
        // System.out.printf("uncover %d\n", i);
        INode ii = inodes.get(i);
        int l = ii.llink;
        int r = ii.rlink;
        inodes.get(l).rlink = i;
        inodes.get(r).llink = i;
        int p = xnodes.get(i).ulink;
        while (p != i) {
            unhide(p);
            p = xnodes.get(p).ulink;
        }
    }

    private void unhide(int p) {
        // System.out.printf("unhide %d\n", p);
        int q = p - 1;
        while (q != p) {
            XNode xq = xnodes.get(q);
            int x = xq.top;
            int u = xq.ulink;
            int d = xq.dlink;
            if (x <= 0) {
                q = d;  // q was a spacer
            } else {
                xnodes.get(u).dlink = q;
                xnodes.get(d).ulink = q;
                ++xnodes.get(x).len;
                --q;
            }
        }
    }

    private void print() {
        System.out.println("INodes");
        for (INode i : inodes) {
            System.out.printf("%s %d %d\n", i.name, i.llink, i.rlink);
        }
        System.out.println("XNodes");
        for (int i = 0; i < xnodes.size(); ++i) {
            XNode x = xnodes.get(i);
            System.out.printf("%d: %d %s %d %d\n", i, x.len, x.top > 0 ? inodes.get(x.top).name : x.top, x.ulink, x.dlink);
        }
    }

    /**
     * Solve the exact cover problem. Announces each solution via supplied callback. Returns when
     * all solutions (zero or more) have been found.
     */
    public void solve(Function<List<Integer>, Boolean> onSolution) {
        // print();
        if (state == State.ADDING_OPTIONS) state = State.SOLVING;
        if (state != State.SOLVING) throw new IllegalStateException("cannot start solving now");
        int[] x = new int[optionCount];
        int i = 0;
        int l = 0;
        int step = 2;

        STEP: while (true) {
            switch (step) {
                // The cases are numbered in accordance with Algorithm D's steps. The switch
                // is used to accomplish the go-tos between steps.
                case 2:  // Enter level l.
                    if (inode0.rlink == 0) {
                        // visit
                        ArrayList<Integer> solution = Lists.newArrayListWithCapacity(l);
                        for (int k = 0; k < l; ++k) {
                            // Any x_i might be in the middle of an option; walk backward
                            // to find the start of the option.
                            int xk = x[k];
                            while (xnodes.get(xk).top > 0) --xk;
                            solution.add(-xnodes.get(xk).top);
                        }
                        boolean proceed = onSolution.apply(solution);
                        if (!proceed) break STEP;
                        step = 8;
                        continue STEP;
                    }
                // case 3:  // Choose i.
                    switch (strategy) {
                        case FIRST:
                            i = inode0.rlink;
                            break;
                        case MRV:
                            int minLen = Integer.MAX_VALUE;
                            for (int ic = inode0.rlink; ic != 0; ic = inodes.get(ic).rlink) {
                                int len = xnodes.get(ic).len;
                                if (len < minLen) {
                                    minLen = len;
                                    i = ic;
                                }
                            }
                            break;
                    }
                // case 4:  // Cover i.
                    cover(i);
                    x[l] = xnodes.get(i).dlink;
                case 5:  // Try x[l].
                    if (x[l] == i) {
                        step = 7;
                        continue STEP;
                    }
                    for (int p = x[l] + 1; p != x[l]; ) {
                        int j = xnodes.get(p).top;
                        if (j <= 0) {
                            p = xnodes.get(p).ulink;
                        } else {
                            cover(j);
                            ++p;
                        }
                    }
                    ++l;
                    step = 2;
                    continue STEP;
                case 6:  // Try again.
                    for (int p = x[l] - 1; p != x[l]; ) {
                        int j = xnodes.get(p).top;
                        if (j <= 0) {
                            p = xnodes.get(p).dlink;
                        } else {
                            uncover(j);
                            --p;
                        }
                    }
                    i = xnodes.get(x[l]).top;
                    x[l] = xnodes.get(x[l]).dlink;
                    step = 5;
                    continue STEP;
                case 7:  // Backtrack.
                    uncover(i);
                case 8:  // Leave level l.
                    if (l == 0) break STEP;
                    --l;
                    step = 6;
            }
        }
        state = State.COMPLETE;
    }

    /**
     * Gather all solutions, however long that takes, and return them.
     * @return A list of subsets of the set of option indexes (counting from zero) forming the exact covers.
     */
    public List<List<Integer>> allSolutions() {
        List<List<Integer>> solutions = new ArrayList<>();
        solve(s -> {
            solutions.add(s);
            return true;
        });
        return solutions;
    }

    public static ExactCoverProblem parseFrom(String problemDescription) {
        return parseFrom(new StringReader(problemDescription));
    }

    /**
     * Parses a complete problem description. Problem must be in an
     * empty state. The format accepted is that described by Knuth
     * (first line: item names separated by whitespace; each subsequent
     * line is one option, containing a subset of items). The first line
     * may contain a semicolon which separates primary from secondary
     * options.
     * @param problemDescription textual description of XC problem
     * @return a problem instance from which solutions may be generated
     */
    public static ExactCoverProblem parseFrom(Reader problemDescription) {
        // ExactCoverProblem p = new ExactCoverProblem();
        Scanner s = new Scanner(problemDescription);
        if (!s.hasNextLine()) {
            throw new IllegalArgumentException("no item line");
        }
        ExactCoverProblem p = new ExactCoverProblem(splitter.split(s.nextLine()));
        while (s.hasNextLine()) {
            p.addOption(splitter.split(s.nextLine()));
        }
        return p;
    }
}
