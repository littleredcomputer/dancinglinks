package net.littleredcomputer.knuth7;

import com.google.common.base.Stopwatch;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.apache.logging.log4j.message.FormattedMessage;

import java.time.Duration;
import java.time.Instant;
import java.util.Arrays;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

public abstract class AbstractSATSolver {
    protected static final Logger log = LogManager.getFormatterLogger(AbstractSATSolver.class);
    final int logCheckSteps = 1000;
    protected final SATProblem problem;
    private final String name;
    private Duration logInterval = Duration.ofMillis(1000);
    private Instant lastLogTime = Instant.EPOCH;
    private Stopwatch stopwatch = Stopwatch.createUnstarted();

    public void setLogInterval(Duration interval) { logInterval = interval; }

    AbstractSATSolver(String name, SATProblem problem) {
        this.name = name;
        this.problem = problem;
    }

    void start() {
        stopwatch.start();
        lastLogTime = Instant.now();
    }

    private final static int initialStateSegment = 81;
    private final static int finalStateSegment = 16;
    private String stateToString(int[] state) {
        StringBuilder s = new StringBuilder();
        IntStream is = Arrays.stream(state);
        if (state.length > 100) {
            is.limit(initialStateSegment).forEach(s::append);
            s.append("...");
            is.skip(state.length-initialStateSegment-finalStateSegment).forEach(s::append);
        } else {
            is.forEach(s::append);
        }
        return s.toString();
    }

    void maybeReportProgress(int steps, int[] m) {
        Instant now = Instant.now();
        if (Duration.between(lastLogTime, now).compareTo(logInterval) < 0) return;
        log.info(() -> new FormattedMessage("%s: %s %d steps. state %s", name, stopwatch, steps, stateToString(m)));
        lastLogTime = now;
    }
    public abstract Optional<boolean[]> solve();
}
