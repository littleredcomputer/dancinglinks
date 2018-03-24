package net.littleredcomputer.knuth7;

import com.google.common.base.Stopwatch;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.apache.logging.log4j.message.FormattedMessage;

import java.time.Duration;
import java.time.Instant;
import java.util.Optional;
import java.util.function.Supplier;

public abstract class AbstractSATSolver {
    protected static final Logger log = LogManager.getFormatterLogger(AbstractSATSolver.class);
    final int logCheckSteps = 1000;
    protected final SATProblem problem;
    protected long stepCount;
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
        if (state.length > 100) {
            for (int i = 0; i < initialStateSegment; ++i)  s.append(state[i]);
            s.append("...");
            for (int i = state.length-finalStateSegment; i < state.length; ++i) s.append(state[i]);
        } else {
            for (int i = 0; i < state.length; ++i) s.append(state[i]);
        }
        return s.toString();
    }

    void maybeReportProgress(Supplier<String> s) {
        Instant now = Instant.now();
        if (Duration.between(lastLogTime, now).compareTo(logInterval) < 0) return;
        log.info(() -> new FormattedMessage("%s %d steps %s %s", name, stepCount, stopwatch, s.get()));
        lastLogTime = now;
    }

    void maybeReportProgress(int[] m) {
        maybeReportProgress(() -> stateToString(m));
    }

    public abstract Optional<boolean[]> solve();
}
