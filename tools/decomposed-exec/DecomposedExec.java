/**
 * DecomposedExec — minimal driver exposing capabilities the Alloy 6 CLI hides
 * (DT-024 §9 spike): Pardinus DECOMPOSED parallel solving (A4Options.decompose_mode /
 * decompose_threads) and, groundwork for the core experiment, coreMinimization.
 *
 * The stock `alloy.jar exec` surfaces neither; both live in the public A4Options API.
 *
 * Usage:
 *   javac -cp <alloy.jar> DecomposedExec.java
 *   java  -cp <alloy.jar>:<dir> DecomposedExec <file.als> <command-label> <mode> <threads> [solver]
 *     mode:    0 = off (baseline), 1 = hybrid, 2 = parallel (GUI "decompose strategy" values)
 *     threads: Pardinus decompose thread count (ignored when mode = 0)
 *     solver:  optional SATFactory name (default: the jar's default; list via `alloy.jar solvers`)
 *
 * Prints one line per matched command: label, satisfiable, wall ms — enough for A/B
 * timing against the plain CLI on the same command.
 */
import java.util.Optional;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;
import kodkod.engine.satlab.SATFactory;

public class DecomposedExec {

    public static void main(String[] args) throws Exception {
        if (args.length < 4) {
            System.err.println("usage: DecomposedExec <file.als> <command-label> <mode 0|1|2> <threads> [solver]");
            System.exit(2);
        }
        String file = args[0];
        String label = args[1];
        int mode = Integer.parseInt(args[2]);
        int threads = Integer.parseInt(args[3]);

        A4Reporter rep = new A4Reporter();
        CompModule world = CompUtil.parseEverything_fromFile(rep, null, file);

        A4Options opt = new A4Options();
        opt.originalFilename = file;
        opt.decompose_mode = mode;
        opt.decompose_threads = threads;
        if (args.length > 4) {
            Optional<SATFactory> f = SATFactory.find(args[4]);
            if (f.isEmpty()) {
                System.err.println("unknown solver '" + args[4] + "'");
                System.exit(2);
            }
            opt.solver = f.get();
        }

        boolean matched = false;
        for (Command c : world.getAllCommands()) {
            if (!c.label.equals(label))
                continue;
            matched = true;
            long t0 = System.currentTimeMillis();
            A4Solution sol = TranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), c, opt);
            long ms = System.currentTimeMillis() - t0;
            System.out.println(c.label + "\tsat=" + sol.satisfiable() + "\tmode=" + mode + "\tthreads=" + threads + "\tms=" + ms);
        }
        if (!matched) {
            System.err.println("no command labeled '" + label + "' in " + file);
            System.exit(2);
        }
    }
}
