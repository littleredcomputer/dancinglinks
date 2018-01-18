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
        private final int[] llink = new int[items.size() + 1];
        private final int[] rlink = new int[items.size() + 1];
        private final int[] len = new int[items.size()];
        private final int[] ulink;
        private final int[] dlink;
        private final int[] top;

        Solutions() {
            for (int i = 1; i < llink.length; ++i) {
                rlink[i-1] = i;
                llink[i] = i-1;
            }
            llink[N+1] = N;
            rlink[N] = N+1;
            llink[N1+1] = N+1;
            rlink[N+1] = N1+1;
            llink[0] = N1;
            rlink[N1] = 0;

            int nxnodes = items.size() + options.size() + 1;  // all the headers + all the spacers
            for (List<Integer> l : options) {
                nxnodes += l.size();
            }
            ulink = new int[nxnodes];
            dlink = new int[nxnodes];
            top = new int[nxnodes];

            for (int i = 0; i < ulink.length; ++i) {
                ulink[i] = dlink[i] = i;
            }

            int M = 0;
            int p = N+1;
            top[p] = 0;
            int q;

            for (List<Integer> o : options) {
                for (int j = 1; j <= o.size(); ++j) {
                    int ij = o.get(j-1);
                    ++len[ij];

                    q = ulink[ij];
                    ulink[p+j] = q;
                    dlink[q] = p+j;
                    dlink[p+j] = ij;
                    ulink[ij] = p+j;
                    top[p+j] = ij;
                }
                final int k = o.size();
                ++M;
                dlink[p] = p+k;
                p += k+1;
                top[p] = -M;
                ulink[p] = p-k;
            }
        }


        private void hide(int p) {
            // System.out.printf("hide %d\n", p);
            int q = p + 1;
            while (q != p) {
                int x = top[q];
                int u = ulink[q];
                int d = dlink[q];
                if (x <= 0) {
                    q = u;
                } else {
                    dlink[u] = d;
                    ulink[d] = u;
                    --len[x];
                    ++q;
                }
            }
        }

        private void cover(int i) {
            // System.out.printf("cover %d\n", i);
            int p = dlink[i];
            while (p != i) {
                hide(p);
                p = dlink[p];
            }
            int l = llink[i];
            int r = rlink[i];
            rlink[l] = r;
            llink[r] = l;
        }

        private void uncover(int i) {
            // System.out.printf("uncover %d\n", i);
            int l = llink[i];
            int r = rlink[i];
            rlink[l] = i;
            llink[r] = i;
            int p = ulink[i];
            while (p != i) {
                unhide(p);
                p = ulink[p];
            }
        }

        private void unhide(int p) {
            // System.out.printf("unhide %d\n", p);
            int q = p - 1;
            while (q != p) {
                int x = top[q];
                int u = ulink[q];
                int d = dlink[q];
                if (x <= 0) {
                    q = d;  // q was a spacer
                } else {
                    dlink[u] = q;
                    ulink[d] = q;
                    ++len[x];
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
                        if (rlink[0] == 0) {
                            // visit
                            ArrayList<Integer> solution = Lists.newArrayListWithCapacity(l);
                            for (int k = 0; k < l; ++k) {
                                // Any x_i might be in the middle of an option; walk backward
                                // to find the start of the option.
                                int xk = x[k];
                                while(top[xk] > 0) --xk;
                                solution.add(-top[xk]);
                            }
                            step = 8;
                            action.accept(solution);
                            return true;
                        }
                        // case 3:  // Choose i.
                        switch (strategy) {
                            case FIRST:
                                i = rlink[0];
                                break;
                            case MRV:
                                int minLen = Integer.MAX_VALUE;
                                for (int ic = rlink[0]; ic != 0; ic = rlink[ic]) {
                                    int l = len[ic];
                                    if (l < minLen) {
                                        minLen = l;
                                        i = ic;
                                    }
                                }
                                break;
                        }
                        // case 4:  // Cover i.
                        cover(i);
                        x[l] = dlink[i];
                    case 5:  // Try x[l].
                        if (x[l] == i) {
                            step = 7;
                            continue STEP;
                        }
                        for (int p = x[l] + 1; p != x[l]; ) {
                            int j = top[p];
                            if (j <= 0) {
                                p = ulink[p];
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
                            int j = top[p];
                            if (j <= 0) {
                                p = dlink[p];
                            } else {
                                uncover(j);
                                --p;
                            }
                        }
                        i = top[x[l]];
                        x[l] = dlink[x[l]];
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
