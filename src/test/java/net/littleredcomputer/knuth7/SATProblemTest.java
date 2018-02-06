package net.littleredcomputer.knuth7;

import org.junit.Test;

import java.io.InputStreamReader;
import java.io.StringReader;
import java.util.Optional;

import static com.github.npathai.hamcrestopt.OptionalMatchers.isPresentAndIs;
import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.*;

public class SATProblemTest {

    @Test
    public void simple() {
        SATProblem.parseFrom(new StringReader("c simple test\nc heh\np cnf 3 2\n1 -3 0\n2 3 -1 0"));
    }

    @Test(expected = IllegalArgumentException.class)
    public void emptyClauseThrows() {
        SATProblem.parseFrom(new StringReader("c empty clause\np cnf 3 3\n1 2 3 0 0 1 2 0"));
    }

    @Test(expected = IllegalArgumentException.class)
    public void literalOutOfBounds() {
        SATProblem.parseFrom(new StringReader("c oob literal\np cnf 3 2\n1 2 3 0\n2 3 4 0"));
    }

    @Test(expected = IllegalArgumentException.class)
    public void tooManyClauses() {
        SATProblem.parseFrom(new StringReader("c oob clause\np cnf 3 2\n1 2 3 0\n2 3 -1 0\n-2 -3 0"));
    }

    @Test(expected = IllegalArgumentException.class)
    public void danglingClause() {
        SATProblem.parseFrom(new StringReader("c oob clause\np cnf 3 2\n1 2 3 0\n2 3 -1 0\n-2 -3"));
    }

    @Test
    public void ex7() {
        assertThat(SATProblem.parseFrom(new StringReader("p cnf 4 7\n1 2 -3 0 2 3 -4 0 3 4 1 0 4 -1 2 0 -1 -2 3 0 -2 -3 4 0 -3 -4 -1 0")).algorithmA(),
               isPresentAndIs(new boolean[] {false, true, false, true}));
    }

    @Test
    public void ex6() {
        assertThat(SATProblem.parseFrom(new StringReader("p cnf 4 8\n1 2 -3 0 2 3 -4 0 3 4 1 0 4 -1 2 0 -1 -2 3 0 -2 -3 4 0 -3 -4 -1 0 -4 1 -2 0")).algorithmA(),
                is(Optional.empty()));
    }

    private SATProblem fromResource(String name) {
        return SATProblem.parseFrom(new InputStreamReader(this.getClass().getClassLoader().getResourceAsStream(name)));
    }

    private String toBinaryString(boolean[] bs) {
        StringBuilder s = new StringBuilder();
        for (boolean b : bs) s.append(b ? '1' : '0');
        return s.toString();
    }

    @Test
    public void zebra() {
        assertThat(fromResource("zebra.cnf").algorithmA().map(this::toBinaryString),
                isPresentAndIs("00100000011000000010010000000110000000100100000100100000100000010001000000110000010000010000010000010000110000000100010001000001000000001010010000011010010"));
    }

    @Test
    public void hole6() {
        assertThat(fromResource("hole6.cnf").algorithmA(), is(Optional.empty()));
    }

    @Test
    public void quinn() {
        assertThat(fromResource("quinn.cnf").algorithmA().map(this::toBinaryString),
                isPresentAndIs("1010111110111001"));
    }

    // Too hard for algorithm A
    //    @Test
    //    public void dubois20() {
    //        assertThat(SATProblem.parseFrom(new InputStreamReader(this.getClass().getClassLoader().getResourceAsStream("dubois20.cnf"))).algorithmA(),
    //                is(Optional.empty()));
    //
    //    }

}

