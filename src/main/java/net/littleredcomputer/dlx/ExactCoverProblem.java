package net.littleredcomputer.dlx;

import com.google.common.base.Splitter;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Lists;

import java.io.Reader;
import java.io.StringReader;
import java.util.*;
import java.util.function.Consumer;
import java.util.stream.Collectors;
import java.util.stream.Stream;
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

    private final ImmutableList<String> items;
    private final ImmutableMap<String, Integer> itemIndex;  // inverse of above mapping
    private final List<List<Integer>> options = new ArrayList<>();  // integer to option == subset of item indices

    private final int N;  // N and N1 are as in Knuth
    private final int N1;     // index of last primary item (== N if there are no secondary items)

    private ExactCoverProblem(Iterable<String> items) {
        List<String> is = new ArrayList<>();
        ImmutableMap.Builder<String, Integer> mb = new ImmutableMap.Builder<>();
        Set<String> itemsSeen = new HashSet<>();
        is.add("*UNUSED*");
        boolean secondaryItems = false;
        int lastPrimaryItem = 0;
        for (String item : items) {
            if (item.equals(";")) {
                if (secondaryItems) throw new IllegalArgumentException("tertiary items are not supported");
                if (is.size() < 2) throw new IllegalArgumentException("there must be at least one primary item");
                lastPrimaryItem = is.size() - 1;
                secondaryItems = true;
                continue;
            }
            if (itemsSeen.contains(item)) throw new IllegalArgumentException("duplicate item: " + item);
            itemsSeen.add(item);
            mb.put(item, is.size());
            is.add(item);
        }
        if (is.size() <= 1) throw new IllegalArgumentException("There must be at least one item");
        N = is.size() - 1;
        N1 = lastPrimaryItem > 0 ? lastPrimaryItem : N;
        itemIndex = mb.build();
        this.items = ImmutableList.copyOf(is);
    }

    public Stream<List<Integer>> solutions() {
        return StreamSupport.stream(new Solutions(), false);
    }

    public List<List<String>> optionsToItems(List<Integer> options) {
        return options.stream().map(o ->
                this.options.get(o).stream().map(items::get).collect(Collectors.toList())).collect(Collectors.toList());
    }

    /**
     * Add an option (nonempty subset of established items). Empty options are
     * ignored. Repeated items in an option are ignored. Referring to an unknown
     * option will throw.
     * @param items sequence of item names
     */
    private void addOption(Iterable<String> items) {
        Set<Integer> itemsSeen = new HashSet<>();
        List<Integer> itemsOfOption = new ArrayList<>();

        for (String item : items) {
            Integer ix = itemIndex.get(item);
            if (ix == null) throw new IllegalArgumentException("unknown item: " + item);
            if (itemsSeen.contains(ix)) throw new IllegalArgumentException("item repeated in option: " + item);
            itemsOfOption.add(ix);
            itemsSeen.add(ix);
        }
        if (itemsOfOption.isEmpty()) return;
        options.add(itemsOfOption);
    }

    private class Solutions implements Spliterator<List<Integer>> {

        private final List<INode> inodes = new ArrayList<>();
        private final List<XNode> xnodes = new ArrayList<>();

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

        Solutions() {
            // The first INode is the head of the doubly-linked list of items.
            inodes.add(new INode("*FIRST*"));
            // One header for each item
            for (String item : items) {
                INode i = new INode(item);
                int ix = inodes.size();
                inodes.add(i);
                i.llink = ix - 1;
                inodes.get(ix-1).rlink = ix;
            }
            // The trailing element serves as the head of the doubly-linked list of secondary items, if any are present.
            INode last = new INode("*LAST*");
            last.llink = N;
            inodes.add(last);
            inodes.get(N).rlink = N+1;
            inodes.get(N1+1).llink = N+1;
            inodes.get(N1+1).rlink = N1+1;
            inodes.get(0).llink = N1;
            inodes.get(N1).rlink = 0;
            // Build tableau of xnodes: add first spacer
            xnodes.add(new XNode());
            // Add option head nodes, one for each item
            for (int ix = 1; ix <= N; ++ix) {
                XNode x = new XNode();
                xnodes.add(x);
                x.ulink = x.dlink = ix;
                x.len = 0;
            }
            // Add first spacer after head nodes.
            xnodes.add(new XNode());

            // Add the options.

            for (int oi = 0; oi < options.size(); ++oi) {
                List<Integer> option = options.get(oi);
                XNode leftSpacer = xnodes.get(xnodes.size() - 1);
                XNode rightSpacer = new XNode();
                int ix = 0;
                for (int item : option) {
                    XNode xHead = xnodes.get(item);
                    xHead.len++;
                    XNode x = new XNode();
                    ix = xnodes.size();
                    x.ulink = xHead.ulink;
                    xnodes.get(xHead.ulink).dlink = ix;
                    x.dlink = item;
                    x.top = item;
                    xHead.ulink = ix;
                    if (rightSpacer.ulink == 0) {
                        // The first item in the new option. We take care of two small bookkeeping tasks:
                        // ULINK(x) of a spacer is the adddress of the first node in the option before x
                        rightSpacer.ulink = ix;
                        // An index from option index to first net.littleredcomputer.dlx.XNode in the option
                    }
                    xnodes.add(x);
                }
                leftSpacer.dlink = ix;
                leftSpacer.top = -oi;
                xnodes.add(rightSpacer);
            }
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

        private int step = 2;
        private int i = 0;
        private int l = 0;
        private int[] x = new int[options.size()];

        /**
         * Solve the exact cover problem. Announces each solution via supplied callback. Returns when
         * all solutions (zero or more) have been found.
         */
        @Override
        public boolean tryAdvance(Consumer<? super List<Integer>> action) {
            // print();

            STEP: while (true) {
                switch (step) {
                    // The cases are numbered in accordance with Algorithm D's steps. The switch
                    // is used to accomplish the go-tos between steps.
                    case 2:  // Enter level l.
                        if (inodes.get(0).rlink == 0) {
                            // visit
                            ArrayList<Integer> solution = Lists.newArrayListWithCapacity(l);
                            for (int k = 0; k < l; ++k) {
                                // Any x_i might be in the middle of an option; walk backward
                                // to find the start of the option.
                                int xk = x[k];
                                while (xnodes.get(xk).top > 0) --xk;
                                solution.add(-xnodes.get(xk).top);
                            }
                            step = 8;
                            action.accept(solution);
                            return true;
                        }
                        // case 3:  // Choose i.
                        switch (strategy) {
                            case FIRST:
                                i = inodes.get(0).rlink;
                                break;
                            case MRV:
                                int minLen = Integer.MAX_VALUE;
                                for (int ic = inodes.get(0).rlink; ic != 0; ic = inodes.get(ic).rlink) {
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
                        if (l == 0) return false;
                        --l;
                        step = 6;
                }
            }
        }

        @Override
        public Spliterator<List<Integer>> trySplit() {
            return null;
        }

        @Override
        public long estimateSize() {
            return Long.MAX_VALUE;
        }

        @Override
        public int characteristics() {
            return 0;
        }
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
