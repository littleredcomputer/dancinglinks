package net.littleredcomputer.knuth7;

import com.google.common.base.CharMatcher;
import com.google.common.base.Splitter;

import java.util.Arrays;
import java.util.List;
import java.util.Objects;

public class Life {
    private final static Splitter splitter = Splitter.onPattern("\\s").omitEmptyStrings();
    private final static CharMatcher dot = CharMatcher.anyOf(".\u00b7");
    final int r;
    final int c;
    final boolean x[][];

    Life(int r, int c) {
        this.r = r;
        this.c = c;
        x = new boolean[r][];
        for (int i = 0; i < r; ++i) x[i] = new boolean[c];
    }

    static Life fromDots(String s) {
        List<String> rows = splitter.splitToList(s);
        if (rows.isEmpty()) throw new IllegalArgumentException("bad board");
        int r = rows.size();
        int c = rows.get(0).length();
        for (int i = 1; i < r; ++i) {
            if (rows.get(i).length() != c) throw new IllegalArgumentException("ragged board");
        }
        Life l = new Life(r, c);
        for (int i = 0; i < r; ++i) {
            for (int j = 0; j < c; ++j) {
                l.x[i][j] = !dot.matches(rows.get(i).charAt(j));
            }
        }
        return l;
    }

    private int nu(int i, int j) {
        int n = 0;
        for (int dx = -1; dx <= 1; ++dx) {
            for (int dy = -1; dy <= 1; ++dy) {
                if (dx != 0 || dy != 0) {
                    int R = i + dx, C = j + dy;
                    if (R >= 0 && R < r && C >= 0 && C < c && x[R][C]) ++n;
                }
            }
        }
        return n;
    }

    Life step() {
        Life y = new Life(r, c);
        for (int i = 0; i < r; ++i) {
            for (int j = 0; j < c; ++j) {
                int n = nu(i, j);
                // live: 2 or 3, dead 3.
                y.x[i][j] = x[i][j] ? (n == 2 || n == 3) : n == 3;
            }
        }
        return y;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        Life life = (Life) o;
        return r == life.r && c == life.c && Arrays.deepEquals(x, life.x);
    }

    @Override
    public int hashCode() {
        int result = Objects.hash(r, c);
        result = 31 * result + Arrays.deepHashCode(x);
        return result;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < r; ++i) {
            for (int j = 0; j < c; ++j) {
                sb.append(x[i][j] ? '*' : '\u00b7');
            }
            sb.append('\n');
        }
        return sb.toString();
    }
}
