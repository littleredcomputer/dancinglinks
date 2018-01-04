import com.google.common.collect.ImmutableList;
import org.junit.Test;

import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.*;

public class SudokuTest {
    private final String ex28a =
            "..3 .1. ..." +
                    "415 ... .9." +
                    "2.6 5.. 3.." +
                    "5.. .8. ..9" +
                    ".7. 9.. .32" +
                    ".38 ..4 .6." +
                    "... 26. 4.3" +
                    "... 3.. ..8" +
                    "32. ..7 95.";
    private final String ex28b =
            "... ... 3.." +
                    "1.. 4.. ..." +
                    "... ... 1.5" +
                    "9.. ... ..." +
                    "... ..2 6.." +
                    "... .53 ..." +
                    ".5. 8.. ..." +
                    "... 9.. .7." +
                    ".83 ... .4.";

    @Test
    public void ex28aSolution() {
        ExactCoverProblem p = Sudoku.fromBoardString(ex28a).toProblem();
        Stream<List<List<String>>> results = p.allSolutions().stream().map(s -> s.stream().map(p::optionIndexToItemNames).collect(Collectors.toList()));
        assertThat(results.collect(Collectors.toList()), is(ImmutableList.of(
                ImmutableList.of(
                        ImmutableList.of("p00", "r07", "c07", "b07"),
                        ImmutableList.of("c01", "b31", "p40", "r41"),
                        ImmutableList.of("p01", "r09", "b09", "c19"),
                        ImmutableList.of("r02", "p05", "b12", "c52"),
                        ImmutableList.of("p03", "r04", "b14", "c34"),
                        ImmutableList.of("r05", "p08", "b25", "c85"),
                        ImmutableList.of("r06", "p06", "b26", "c66"),
                        ImmutableList.of("c06", "b66", "p70", "r76"),
                        ImmutableList.of("p07", "r08", "b28", "c78"),
                        ImmutableList.of("c08", "p60", "r68", "b68"),
                        ImmutableList.of("b08", "c18", "p21", "r28"),
                        ImmutableList.of("c09", "b39", "p50", "r59"),
                        ImmutableList.of("r12", "p16", "b22", "c62"),
                        ImmutableList.of("r13", "b13", "p14", "c43"),
                        ImmutableList.of("p13", "r16", "b16", "c36"),
                        ImmutableList.of("c14", "b64", "p71", "r74"),
                        ImmutableList.of("c15", "p61", "r65", "b65"),
                        ImmutableList.of("p15", "r18", "b18", "c58"),
                        ImmutableList.of("c16", "p31", "r36", "b36"),
                        ImmutableList.of("r17", "p18", "b27", "c87"),
                        ImmutableList.of("b17", "p24", "r27", "c47"),
                        ImmutableList.of("b19", "p25", "r29", "c59"),
                        ImmutableList.of("r21", "b21", "p27", "c71"),
                        ImmutableList.of("c21", "b61", "r81", "p82"),
                        ImmutableList.of("c22", "r32", "b32", "p32"),
                        ImmutableList.of("r24", "b24", "p28", "c84"),
                        ImmutableList.of("c24", "b34", "p42", "r44"),
                        ImmutableList.of("c27", "b67", "p72", "r77"),
                        ImmutableList.of("c29", "p62", "r69", "b69"),
                        ImmutableList.of("r31", "c31", "p33", "b41"),
                        ImmutableList.of("r33", "p35", "b43", "c53"),
                        ImmutableList.of("r34", "p37", "b54", "c74"),
                        ImmutableList.of("p36", "r37", "b57", "c67"),
                        ImmutableList.of("c37", "b47", "p53", "r57"),
                        ImmutableList.of("c38", "b78", "p83", "r88"),
                        ImmutableList.of("c42", "b42", "r52", "p54"),
                        ImmutableList.of("c44", "b74", "r84", "p84"),
                        ImmutableList.of("p44", "r45", "c45", "b45"),
                        ImmutableList.of("p45", "r46", "b46", "c56"),
                        ImmutableList.of("p46", "r48", "b58", "c68"),
                        ImmutableList.of("c49", "p74", "r79", "b79"),
                        ImmutableList.of("r51", "b51", "p58", "c81"),
                        ImmutableList.of("c51", "r61", "p65", "b71"),
                        ImmutableList.of("r55", "b55", "p56", "c65"),
                        ImmutableList.of("c55", "r75", "b75", "p75"),
                        ImmutableList.of("c61", "r71", "p76", "b81"),
                        ImmutableList.of("r67", "p67", "c77", "b87"),
                        ImmutableList.of("r72", "c72", "p77", "b82"),
                        ImmutableList.of("r86", "c86", "b86", "p88")))));
    }

    @Test
    public void ex28bSolution() {
        //assertThat(Sudoku.fromBoardString(ex28b).toProblem().allSolutions(), is(98));
    }
}
