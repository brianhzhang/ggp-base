import java.awt.GridLayout;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.List;

import org.ggp.base.apps.player.config.ConfigPanel;
import org.ggp.base.player.gamer.exception.GamePreviewException;
import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.game.Game;
import org.ggp.base.util.match.Match;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.cache.CachedStateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.prover.ProverStateMachine;

public class MyPlayer extends StateMachineGamer {

	public static final int MAX_SCORE = 100;
	public static final int MIN_SCORE = 0;
	public static final int LEGAL = 1;
	public static final int RANDOM = 2;
	public static final int ALPHABETA = 3;
	public static final int HEURISTIC = 4;
	public static final int N_OPTIONS = 10;
	public static final int TIMEOUT_BUFFER = 3000; // time for network
													// communication in ms

	public int method = HEURISTIC;

	private Method player;

	@Override
	public StateMachine getInitialStateMachine() {
		return new CachedStateMachine(new ProverStateMachine());
	}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		if (method == LEGAL) player = new Legal();
		if (method == RANDOM) player = new RandomPlayer();
		if (method == ALPHABETA) player = new AlphaBeta();
		if (method == HEURISTIC) player = new Heuristic();
		player.metaGame(this, timeout - TIMEOUT_BUFFER);
		return;
	}

	@Override
	public Move stateMachineSelectMove(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		StateMachine machine = getStateMachine();
		MachineState state = getCurrentState();
		Role role = getRole();
		List<Move> moves = machine.findLegals(role, state);

		/** legal player **/
		// legal player #1: 8432
		// legal player #2: 1344

		/** random player **/
		// random player #1: 6920
		// random player #2: 1344

		/** alpha beta player **/
		// alpha beta #1: 7234
		// alpha beta #2: 4325

		return player.run(machine, state, role, moves, timeout - TIMEOUT_BUFFER);
	}

	@Override
	public void stateMachineStop() {
		Match m = getMatch();
		StateMachine machine = getStateMachine();
		MachineState state = getCurrentState();
		Role role = getRole();
		List<Role> roles = machine.getRoles();
		String save = "";
		try {
			save = m.getMatchId() + "\t" + method + "\t" + machine.getGoal(state, role);
			for (Role r : roles) {
				if (r.equals(role)) continue;
				save += "\t" + machine.getGoal(state, r);
			}
		} catch (GoalDefinitionException e) {
			save = m.getMatchId();
		}
		saveLine("Game-Logs.txt", save);
		saveLine("Logs/" + m.getMatchId() + ".txt", m.toXML());
		player.cleanUp();
		return;
	}

	public static void saveLine(String fileName, String add) {
		String lines = "";
		BufferedReader inFile = null;
		try {
			inFile = new BufferedReader(new FileReader(fileName));
			String line;
			line = inFile.readLine();
			while (line != null) {
				lines = lines + line + "\n";
				line = inFile.readLine();
			}
			inFile.close();
		} catch (IOException e) {
			System.out.println("The file " + fileName + " was not found.  It will be created.");
		}

		PrintWriter outFile = null;
		try {
			outFile = new PrintWriter(new BufferedWriter(new FileWriter(fileName)));
			outFile.print(lines);
			outFile.print(add);

			outFile.close();
		} catch (IOException e) {
			System.out.println("IOException creating file " + fileName);
			return;
		}
	}

	@Override
	public void stateMachineAbort() {
		player.cleanUp();
		return;
	}

	@Override
	public void preview(Game g, long timeout) throws GamePreviewException {
		return;
	}

	@Override
	public ConfigPanel getConfigPanel() {
		return new Config(new GridLayout(N_OPTIONS, 1), this);
	}

	@Override
	public String getName() {
		return "Brian and Jeff'); DROP TABLE TEAMS; --";
	}
}
