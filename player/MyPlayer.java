import java.awt.GridLayout;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;

import org.ggp.base.apps.player.config.ConfigPanel;
import org.ggp.base.player.gamer.exception.GamePreviewException;
import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.game.Game;
import org.ggp.base.util.gdl.grammar.Gdl;
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

	public static final int EXPERIMENTAL = 0;
	public static final int LEGAL = 1;
	public static final int RANDOM = 2;
	public static final int ALPHABETA = 3;
	public static final int HEURISTIC = 4;
	public static final int MONTECARLO = 5;
	public static final int MCTS = 6;

	public static final int N_OPTIONS = 10;
	public static final int TIMEOUT_BUFFER = 3000; // time for network
	// communication in ms
	public static final int N_THREADS = 4;

	public static final PrintWriter gamelog = getGameLog();
	public int method = 6;
	private Method player;
	List<Gdl> gameDescription;

	private static PrintWriter getGameLog() {
		try {
			return new PrintWriter(new FileWriter("logs/gamelogs.csv", true), true);
		} catch (IOException e) {
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public StateMachine getInitialStateMachine() {
		// return new CachedStateMachine(new ProverStateMachine());
		// return new PropNetStateMachine();
		// return new PropNetStateMachine2();
		// for (int i = 0; i < N_THREADS; i ++) {
		// machines[i] = new BetterPropNetStateMachine(new StateMachine[0]);
		// }
		// return new BetterPropNetStateMachine(machines);
		return new GDLGetter();
	}

	private JustKiddingPropNetStateMachine copyMachine(JustKiddingPropNetStateMachine p) {
		JustKiddingPropNetStateMachine newp = new JustKiddingPropNetStateMachine();
		newp.comps = new int[p.comps.length][];
		for (int i = 0; i < p.comps.length; i++) {
			newp.comps[i] = p.comps[i].clone();
		}
		newp.structure = p.structure;
		newp.roles = p.roles;
		newp.actions = p.actions;
		newp.term = p.term;
		newp.init = p.init;
		newp.basearr = p.basearr;
		newp.inputarr = p.inputarr;
		newp.inputmap = p.inputmap;
		newp.legals = p.legals;
		newp.legalarr = p.legalarr;
		newp.goals = p.goals;
		newp.p = p.p;
		newp.props = p.props;
		return newp;
	}

	public void switchToNewPropnets(JustKiddingPropNetStateMachine machine,
			StateMachine[] machines) {
		switchStateMachine(machine);
		for (int i = 0; i < N_THREADS; i++) {
			machines[i] = copyMachine(machine);
		}
	}

	public void switchToPropnets(BetterMetaPropNetStateMachineFactory m, StateMachine[] machines) {
		StateMachine machine = m.getNewMachine();
		machine.initialize(gameDescription);
		switchStateMachine(machine);
		for (int i = 0; i < N_THREADS; i++) {
			machines[i] = m.getNewMachine();
			machines[i].initialize(gameDescription);
		}
	}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		Log.setFile(getMatch().getMatchId() + "_" + getRole());
		Log.println("");
		gameDescription = ((GDLGetter) getStateMachine()).getDescription();

		StateMachine m = new CachedStateMachine(new ProverStateMachine());
		m.initialize(gameDescription);
		switchStateMachine(m);
		if (method == LEGAL) player = new Legal();
		if (method == RANDOM) player = new RandomPlayer();
		if (method == ALPHABETA) player = new AlphaBeta();
		if (method == HEURISTIC) player = new Heuristic();
		if (method == MONTECARLO) player = new MonteCarlo();
		if (method == MCTS) player = new MCTS(this, gameDescription);
		if (method == EXPERIMENTAL) player = new Experiment(this, gameDescription);
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
		// Log.println(m);
		StateMachine machine = getStateMachine();
		MachineState state = getCurrentState();
		Role role = getRole();
		List<Role> roles = machine.getRoles();
		String save = "";
		try {
			save = String.format("%s,%s,%s,%s", m.getMatchId(), role, method,
					machine.getGoal(state, role));
			for (Role r : roles) {
				if (r.equals(role)) continue;
				save += "," + machine.getGoal(state, r);
			}
		} catch (GoalDefinitionException e) {
			save = m.getMatchId();
		}
		gamelog.println(save);
		player.cleanUp();
		return;
	}

	@Override
	public void stateMachineAbort() {
		stateMachineStop();
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

class GDLGetter extends StateMachine {

	List<Gdl> contents;

	@Override
	public List<Move> findActions(Role role) throws MoveDefinitionException {
		return new ArrayList<Move>();
	}

	public List<Gdl> getDescription() {
		return contents;
	}

	@Override
	public void initialize(List<Gdl> description) {
		this.contents = description;
	}

	@Override
	public int getGoal(MachineState state, Role role) throws GoalDefinitionException {
		return 0;
	}

	@Override
	public boolean isTerminal(MachineState state) {
		return false;
	}

	@Override
	public List<Role> getRoles() {
		return new ArrayList<Role>();
	}

	@Override
	public MachineState getInitialState() {
		return new MachineState();
	}

	@Override
	public List<Move> getLegalMoves(MachineState state, Role role) throws MoveDefinitionException {
		return new ArrayList<Move>();
	}

	@Override
	public MachineState getNextState(MachineState state, List<Move> moves)
			throws TransitionDefinitionException {
		return new MachineState();
	}
}
