package net.littleredcomputer.dlx;

import com.google.common.base.Splitter;
import org.junit.Test;

import java.util.Collections;
import java.util.stream.Collectors;

import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.*;

public class WordFindTest {
    private final Splitter wordSplitter = Splitter.on(' ').omitEmptyStrings();

    @Test
    public void middleEarth() {
        assertThat(new WordFind(8, 8, wordSplitter.split("gandalf frodo boromir merry pippin aragorn samwise legolas gimli gollum ring sauron"))
                .solutions()
                .limit(1)
                .collect(Collectors.toList()), is(Collections.singletonList(
                        "GANDALFB\n" +
                                "SNYRREMO\n" +
                                "APIFAGUR\n" +
                                "MILRGOLO\n" +
                                "WPMOOLLM\n" +
                                "IPIDRAOI\n" +
                                "SIGONSGR\n" +
                                "ENSAURON\n")));
    }

}
