package net.littleredcomputer.knuth7.sat;

import com.google.common.base.Stopwatch;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.apache.logging.log4j.message.FormattedMessage;

import java.time.Duration;
import java.time.Instant;
import java.util.Optional;
import java.util.function.Supplier;

public abstract class AbstractSATSolver {
    private static final Logger log = LogManager.getFormatterLogger(AbstractSATSolver.class);
    final int logCheckSteps = 10000;
    final SATProblem problem;
    long stepCount;
    long nodeCount = 0;  // TODO: make sure the other solvers besides L use this
    private long lastStepCount;
    private final String name;
    private Duration logInterval = Duration.ofMillis(1000);
    private Instant lastLogTime = Instant.EPOCH;
    private final Stopwatch stopwatch = Stopwatch.createUnstarted();

    public void setLogInterval(Duration interval) { logInterval = interval; }

    AbstractSATSolver(String name, SATProblem problem) {
        this.name = name;
        this.problem = problem;
    }

    void start() {
        if (!stopwatch.isRunning()) stopwatch.start();
        lastLogTime = Instant.now();
        lastStepCount = stepCount;
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
            for (int aState : state) s.append(aState);
        }
        return s.toString();
    }

    void maybeReportProgress(Supplier<String> s) {
        Instant now = Instant.now();

        Duration tween = Duration.between(lastLogTime, now);
        if (tween.compareTo(logInterval) < 0) return;
        final double perSec = 1e3 * (stepCount - lastStepCount) / tween.toMillis();
        log.info(() -> new FormattedMessage("%s %d steps %s %.0f/sec %s", name, stepCount, stopwatch, perSec, s.get()));
        lastLogTime = now;
        lastStepCount = stepCount;
    }

    void maybeReportProgress(int[] m) {
        maybeReportProgress(() -> stateToString(m));
    }

    public abstract Optional<boolean[]> solve();

    static int thevar(int literal) { return literal >> 1; }
    static int poslit(int variable) { return 2*variable; }
    static int neglit(int variable) { return 2*variable+1; }
    static int not(int l) { return l^1; }
    static boolean negated(int l) { return (l & 1) != 0; }
}
