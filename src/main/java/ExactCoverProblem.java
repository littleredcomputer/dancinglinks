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
    private static final Splitter splitter = Splitter.on(" ").omitEmptyStrings();

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
    // private final INode inodes;
    private final INode inode0 = new INode();
    private final ArrayList<INode> inodes = Lists.newArrayList(inode0);
    private final ArrayList<XNode> xnodes = new ArrayList<>();
    private final ArrayList<Integer> optionByNumber = new ArrayList<>();
    private int optionCount = 0;
    private Function<List<Integer>, Boolean> reporter;
    private Runnable complete;

    ExactCoverProblem() {}

    private boolean defaultReport(List<Integer> options) {
        System.out.println("SOLUTION");
        for (int k: options) {
            System.out.print("  ");
            for (int p = k; xnodes.get(p).top > 0; ++p) {
                System.out.print(inodes.get(xnodes.get(p).top).name + " ");
            }
            System.out.println();
        }
        return true;
    }

    public List<String> optionIndexToItemNames(int oi) {
        List<String> items = new ArrayList<>();
        for (int ix = optionByNumber.get(oi); xnodes.get(ix).top > 0; ++ix) {
            items.add(inodes.get(xnodes.get(ix).top).name);
        }
        return items;
    }

    private void addItem(String name) {
        if (state != State.ADDING_ITEMS) {
            throw new IllegalStateException("cannot add more items now");
        }
        if (itemIndex.containsKey(name)) {
            throw new IllegalArgumentException("item name " + name + " already used");
        }
        final int ix = inodes.size();
        INode i = new INode();
        inodes.add(i);
        itemIndex.put(name, ix);
        i.name = name;
        i.llink = inode0.llink;
        inodes.get(inode0.llink).rlink = ix;
        i.rlink = 0;
        inodes.get(0).llink = ix;
    }

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
        // Sort the items in the option with respect to the order in which the items
        // were introduced. In this way the representative item chosen for an option
        // will be the left-most.
        List<Integer> indices = StreamSupport.stream(items.spliterator(), false)
                .map(itemIndex::get)
                .sorted()
                .collect(Collectors.toList());

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
                // An index from option index to first XNode in the option
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
        if (complete != null) complete.run();
    }

    /**
     * Gather all solutions, however long that takes, and return them.
     * @return
     */
    public List<List<Integer>> allSolutions() {
        List<List<Integer>> solutions = new ArrayList<>();
        solve(s -> {
            solutions.add(s);
            return true;
        });
        return solutions;
    }

    public ExactCoverProblem parse(String problemDescription) {
        return parse(new StringReader(problemDescription));
    }

    /**
     * Parses a complete problem description. Problem must be in an
     * empty state. The format accepted is that described by Knuth
     * (first line: item names separated by whitespace; each subsequent
     * line is one option, containing a subset of items).
     * @param problemDescription
     * @return
     */
    public ExactCoverProblem parse(Reader problemDescription) {
        if (state != State.ADDING_ITEMS || inodes.size() > 1) {
            throw new IllegalStateException("parse is used to provide the complete problem description");
        }
        Scanner s = new Scanner(problemDescription);
        if (!s.hasNextLine()) {
            throw new IllegalArgumentException("no item line");
        }
        ArrayList<String> items = Lists.newArrayList(splitter.split(s.nextLine()));
        if (items.size() < 1) {
            throw new IllegalArgumentException("no items");
        }
        for (String i : items) {
            addItem(i);
        }
        while (s.hasNextLine()) {
            String l = s.nextLine();
            addOption(splitter.split(l));
        }
        state = State.SOLVING;
        return this;
    }
}
