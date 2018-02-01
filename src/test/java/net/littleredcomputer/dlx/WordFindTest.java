// Copyright 2018 Colin Smith. MIT License.
package net.littleredcomputer.dlx;

import org.junit.Test;

import java.time.Duration;
import java.util.Arrays;
import java.util.Collections;
import java.util.stream.Collectors;

import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertThat;

public class WordFindTest {
    @Test
    public void middleEarth() {
        assertThat(new WordFind(8, 8,
                Arrays.asList("gandalf", "frodo", "boromir", "merry", "pippin", "aragorn", "samwise", "legolas", "gimli", "gollum", "ring", "sauron"))
                .setLogInterval(Duration.ofMillis(300))
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
