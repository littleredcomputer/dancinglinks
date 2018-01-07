import com.google.common.collect.ImmutableList;
import org.junit.Test;

import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.*;

public class SudokuTest {

    @Test
    public void ex28aSolution() {
        String ex28a = "..3 .1. ... " +
                "415 ... .9. " +
                "2.6 5.. 3.. " +
                "5.. .8. ..9 " +
                ".7. 9.. .32 " +
                ".38 ..4 .6. " +
                "... 26. 4.3 " +
                "... 3.. ..8 " +
                "32. ..7 95. ";
        assertThat(Sudoku.fromBoardString(ex28a).solve(),
                is(ImmutableList.of("793 412 685 415 638 297 286 579 314 562 183 749 174 956 832 938 724 561 859 261 473 647 395 128 321 847 956 ")));
    }

    @Test
    public void ex28bSolution() {
        String ex28b = "... ... 3.." +
                "1.. 4.. ... " +
                "... ... 1.5 " +
                "9.. ... ... " +
                "... ..2 6.. " +
                "... .53 ... " +
                ".5. 8.. ... " +
                "... 9.. .7. " +
                ".83 ... .4. ";
        assertThat(Sudoku.fromBoardString(ex28b).solve(),
                is(ImmutableList.of("597 218 364 132 465 897 864 379 125 915 684 732 348 792 651 276 153 489 659 847 213 421 936 578 783 521 946 ")));
    }

    @Test
    public void ex28cSolutions() {
        String ex28c = ".3. .1. ... " +
                "... 4.. 1.." +
                ".5. ... .9." +
                "2.. ... 6.4" +
                "... .35 ..." +
                "1.. ... ..." +
                "4.. 6.. ..." +
                "... ... .5." +
                ".9. ... ...";
        assertThat(Sudoku.fromBoardString(ex28c).solve(),
                is(ImmutableList.of("934 518 267 762 493 185 851 762 493 285 971 634 649 235 718 173 846 529 418 659 372 327 184 956 596 327 841 ",
                        "934 517 268 862 493 175 751 862 493 275 981 634 649 235 817 183 746 529 417 659 382 328 174 956 596 328 741 ")));
    }

    @Test
    public void supposedlyHardOne() {
        String h = "..4 8.. ..7 .5. .1. .9. 1.. ..9 6.. 3.. ..4 5.. .4. .8. .3. ..8 2.. ..9 ..6 1.. ..4 .2. .3. .6. 5.. ..6 2..";
        assertThat(Sudoku.fromBoardString(h).solve(),
                is(ImmutableList.of("694 825 317 853 617 492 172 349 685 319 764 528 245 981 736 768 253 149 936 172 854 427 538 961 581 496 273 ")));
    }
}
