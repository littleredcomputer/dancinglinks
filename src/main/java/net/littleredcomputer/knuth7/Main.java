package net.littleredcomputer.knuth7;

import com.google.common.base.Joiner;
import com.google.common.base.Splitter;
import com.google.common.base.Stopwatch;
import com.google.common.collect.Lists;
import javafx.util.Pair;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

import java.io.*;
import java.time.Duration;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

public class Main {
    private static Joiner spaceJoiner = Joiner.on(' ');
    private static Splitter commaSplitter = Splitter.on(',');
    private static Pattern langfordRe = Pattern.compile("langford(\\d+)");
    private static Pattern waerdenRe = Pattern.compile("waerden(\\d+,\\d+,\\d+)");

    private static Options options() {
        return new Options()
                .addOption("task", true, "type of problem to solve")
                .addOption("problem", true, "filename of problem description")
                .addOption("format", true, "format of problem file")
                .addOption("board", true, "sudoku board [1-9.]{81}")
                .addOption("width", true, "width")
                .addOption("height", true, "height")
                .addOption("words", true, "words to fit")
                .addOption("loginterval", true, "interval between progress log entries in ISO-8601 format");
    }

    private static Reader problem(CommandLine cmd) throws FileNotFoundException {
        if (!cmd.hasOption("problem")) throw new IllegalArgumentException("Must specify -problem");
        String p = cmd.getOptionValue("problem");
        return new BufferedReader(p.equals("-") ? new InputStreamReader(System.in) : new FileReader(p));
    }

    private static SATProblem satProblem(CommandLine cmd) throws FileNotFoundException {
        if (!cmd.hasOption("problem")) throw new IllegalArgumentException("Must specify -problem");
        String p = cmd.getOptionValue("problem");
        Matcher lm = langfordRe.matcher(p);
        if (lm.matches()) {
            return SATProblem.langford(Integer.parseInt(lm.group(1)));
        }
        Matcher wm = waerdenRe.matcher(p);
        if (wm.matches()) {
            return SATProblem.waerden(Integer.parseInt(wm.group(1)),
                    Integer.parseInt(wm.group(2)),
                    Integer.parseInt(wm.group(3)));
        }
        // Didn't match a canned problem generator; try a file
        Reader r = problem(cmd);
        switch (cmd.getOptionValue("format", "cnf")) {
            case "cnf": return SATProblem.parseFrom(r);
            case "knuth": return SATProblem.parseKnuth(r);
            default: throw new IllegalArgumentException("unknown problem format");
        }
    }

    private static Function<SATProblem, AbstractSATSolver> solver(CommandLine cmd) {
        if (!cmd.hasOption("algorithm")) return SATAlgorithmA::new;
        String a = cmd.getOptionValue("algorithm");
        switch (a) {
            case "A": return SATAlgorithmA::new;
            case "B": return SATAlgorithmB::new;
            case "D": return SATAlgorithmD::new;
            case "L": return SATAlgorithmL::new;
            case "L3": return p -> new SATAlgorithmL(p.to3SAT());
            default: throw new IllegalArgumentException("Unknown algorithm: " + a);
        }
    }

    private static Stream<Pair<Integer, Integer>> boxSizeStream() {
        return Stream.generate(new Supplier<Pair<Integer, Integer>>() {
            int width = 2;
            int height = 2;

            @Override
            public Pair<Integer, Integer> get() {
                Pair<Integer, Integer> p = new Pair<>(width, height);
                if (height == width) {
                    ++width;
                    height = 2;
                } else {
                    ++height;
                }
                return p;
            }
        });
    }

    private static Duration logInterval(CommandLine cmd) {
        return Duration.parse(cmd.getOptionValue("loginterval", "PT0.1S"));
    }

    public static void main(String[] args) throws ParseException, FileNotFoundException {
        CommandLine cmd = new DefaultParser().parse(options(), args);
        if (!cmd.hasOption("task")) throw new IllegalArgumentException("Must specify -task");
        String task = cmd.getOptionValue("task");
        switch (task) {
            case "exactcover": {
                ExactCoverProblem p = ExactCoverProblem.parseFrom(problem(cmd));
                p.solutions().map(p::optionsToItems).map(s -> s.stream().map(spaceJoiner::join)).forEach(s -> {
                    s.forEach(System.out::println);
                    System.out.println();
                });
                break;
            }
            case "sudoku":
                Sudoku.fromBoardString(cmd.getOptionValue("board")).solutions().forEach(System.out::println);
                break;
            case "wordfind":
                int w = Integer.parseInt(cmd.getOptionValue("width"));
                int h = Integer.parseInt(cmd.getOptionValue("height"));
                List<String> words = commaSplitter.splitToList(cmd.getOptionValue("words"));
                if (w == 0 && h == 0) {
                    long distinctCh = words.stream()
                            .flatMap(s->Lists.charactersOf(s.toUpperCase()).stream())
                            .distinct()
                            .count();
                    long maxWordLen = words.stream().map(String::length).max(Integer::compare).orElse(0);
                    System.out.println("distinct chars " + distinctCh);
                    System.out.println("longest word " + maxWordLen);
                    final boolean[] found = new boolean[] {false};
                    // consider letting the fixed-size case be handled with Stream.of(size)
                    for (Pair<Integer, Integer> wh : (Iterable<Pair<Integer, Integer>>) boxSizeStream()::iterator) {
                        w = wh.getKey();
                        h = wh.getValue();
                        if (w*h < distinctCh || (w < maxWordLen && h < maxWordLen)) {
                            System.out.println(w + "x" + h + " is too small");
                            continue;
                        }
                        new WordFind(w, h, words).solutions().forEach(s -> {
                            System.out.println(s);
                            found[0] = true;
                        });
                        if (found[0]) break;
                        else System.out.println("no solution found for size " + wh.getKey() + "x" + wh.getValue());
                    }
                } else {
                    new WordFind(w, h, words)
                            .setLogInterval(logInterval(cmd))
                            .solutions()
                            .forEach(System.out::println);
                }
                break;
            case "sat": {
                SATProblem p = SATProblem.parseFrom(problem(cmd));
                Stopwatch sw = Stopwatch.createStarted();
                AbstractSATSolver s = solver(cmd).apply(p);
                s.setLogInterval(logInterval(cmd));
                Optional<boolean[]> outcome = s.solve();
                sw.stop();
                System.out.println("c " + sw);
                if (outcome.isPresent()) {
                    System.out.println("s SATISFIABLE");
                    System.out.print("v ");
                    boolean[] bs = outcome.get();
                    for (int i = 0; i < bs.length; ++i) System.out.printf("%d ", bs[i] ? i+1 : -i-1);
                    System.out.println("0");
                } else {
                    System.out.println("s UNSATISFIABLE");
                }
                break;
            }
            case "to3sat": {
                SATProblem p = satProblem(cmd).to3SAT();
                System.out.println("~~ " + Joiner.on(" ").join(args));
                for (int i = 0; i < p.nClauses(); ++i) {
                    List<Integer> c = p.getClause(i);
                    for (int l : c) {
                        System.out.printf("%s%d ", l < 0 ? "~": "", Math.abs(l));
                    }
                    System.out.println();
                }
                break;
            }
            default:
                throw new IllegalArgumentException("unknown task: " + task);
        }
    }
}
