package net.littleredcomputer.dlx;

import com.google.common.base.Joiner;
import com.google.common.base.Splitter;
import org.apache.commons.cli.*;

import java.io.*;

public class Main {
    private static Joiner spaceJoiner = Joiner.on(' ');
    private static Splitter commaSplitter = Splitter.on(',');

    private static Options options() {
        return new Options()
                .addOption("task", true, "type of problem to solve")
                .addOption("problem", true, "filename of problem description")
                .addOption("board", true, "sudoku board [1-9.]{81}")
                .addOption("width", true, "width")
                .addOption("height", true, "height")
                .addOption("words", true, "words to fit");
    }

    private static Reader problem(CommandLine cmd) throws FileNotFoundException {
        if (!cmd.hasOption("problem")) throw new IllegalArgumentException("Must specify --problem");
        String p = cmd.getOptionValue("problem");
        return new BufferedReader(p.equals("-")
                ? new InputStreamReader(System.in)
                : new FileReader(p));
    }

    public static void main(String[] args) throws ParseException, FileNotFoundException {
        CommandLine cmd = new DefaultParser().parse(options(), args);
        if (!cmd.hasOption("task")) throw new IllegalArgumentException("Must specify --task");
        String task = cmd.getOptionValue("task");
        if (task.equals("exactcover")) {
            ExactCoverProblem p = ExactCoverProblem.parseFrom(problem(cmd));
            p.solutions().map(p::optionsToItems).map(s -> s.stream().map(spaceJoiner::join)).forEach(s -> {
                s.forEach(System.out::println);
                System.out.println();
            });
        } else if (task.equals("sudoku")) {
            Sudoku.fromBoardString(cmd.getOptionValue("board")).solutions().forEach(System.out::println);
        } else if (task.equals("wordfind")) {
            int w = Integer.parseInt(cmd.getOptionValue("width"));
            int h = Integer.parseInt(cmd.getOptionValue("height"));
            new WordFind(w, h, commaSplitter.splitToList(cmd.getOptionValue("words")))
                    .solutions()
                    .forEach(System.out::println);
        } else {
            throw new IllegalArgumentException("unknown task: " + task);
        }
    }
}
