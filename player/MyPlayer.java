import java.awt.GridLayout;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import org.ggp.base.apps.player.config.ConfigPanel;
import org.ggp.base.player.gamer.exception.GamePreviewException;
import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.game.Game;
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
	public static final int N_OPTIONS = 10;

	public int method = ALPHABETA;

	private class Bound {
		int lower = MIN_SCORE;
		int upper = MAX_SCORE;
	}

	private Map<MachineState, Bound> cache = new HashMap<>();

	private int stats_nnodes = 0;
	private int stats_ncachehits = 0;

	@Override
	public StateMachine getInitialStateMachine() {
		return new CachedStateMachine(new ProverStateMachine());
	}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		return;
	}

	@Override
	public Move stateMachineSelectMove(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		StateMachine machine = getStateMachine();
		MachineState state = getCurrentState();
		Role role = getRole();

		List<Move> moves = new ArrayList<Move>(machine.findLegals(role, state));
		Collections.shuffle(moves);
		if (moves.size() == 1) return moves.get(0);

		/** legal player **/
		// legal player #1: 8432
		// legal player #2: 1344
		if (method == LEGAL) {
			return moves.get(0);
		}
		/** random player **/
		// random player #1: 6920
		// random player #2: 1344
		// Random random = new Random();
		else if (method == RANDOM) {
			Random random = new Random();
			return moves.get(random.nextInt(moves.size())); // random player
		}

		/** alpha beta player **/
		// alpha beta #1: 7234
		// alpha beta #2: 4325
		else if (method == ALPHABETA) {
			stats_nnodes = 0;
			stats_ncachehits = 0;
			Move bestMove = moves.get(0);
			int bestScore = MIN_SCORE;
			for (Move move : moves) {
				System.out.println("Analyzing move " + move);
				int score = minscore(machine, state, role, move, bestScore, MAX_SCORE);
				if (score > bestScore) {
					bestMove = move;
					bestScore = score;
					if (score == MAX_SCORE) break;
				}
			}
			System.out.printf("time=%d bestmove=%s score=%d nodes=%d cachehits=%d cachesize=%d\n",
					timeout - System.currentTimeMillis(), bestMove, bestScore, stats_nnodes,
					stats_ncachehits, cache.size());
			return bestMove;
		} else {
			return moves.get(0);
		}
	}

	// as seen in notes ch. 6
	private int maxscore(StateMachine machine, MachineState state, Role role, int alpha, int beta)
			throws GoalDefinitionException, MoveDefinitionException, TransitionDefinitionException {
		stats_nnodes++;
		if (machine.isTerminal(state)) return machine.findReward(role, state);
		Bound bound = cache.get(state);
		if (bound == null) {
			bound = new Bound();
			cache.put(state, bound);
		} else { // retrieve cache value
			stats_ncachehits++;
			if (bound.lower >= beta) return beta;
			if (bound.upper <= alpha) return alpha;
			if (bound.lower == bound.upper) return bound.lower;
			// stats_ncachehits--;
			alpha = Math.max(alpha, bound.lower);
			beta = Math.min(beta, bound.upper);
		}
		List<Move> actions = machine.findLegals(role, state);

		int a = alpha; // store original alpha value
		for (Move move : actions) {
			int score = minscore(machine, state, role, move, a, beta);
			a = Math.max(a, score);
			if (a >= beta) break;
		}
		if (a < beta) bound.upper = a;
		if (a > alpha) bound.lower = a;
		return a;
	}

	// as seen in notes ch 6
	private int minscore(StateMachine machine, MachineState state, Role role, Move move, int alpha,
			int beta) throws GoalDefinitionException, MoveDefinitionException,
					TransitionDefinitionException {
		// use joint moves so that we can deal with n-player games; n != 2
		for (List<Move> jmove : machine.getLegalJointMoves(state, role, move)) {
			MachineState next = machine.getNextState(state, jmove);
			int score = maxscore(machine, next, role, alpha, beta);
			beta = Math.min(beta, score);
			if (alpha >= beta) return alpha;
		}
		return beta;
	}

	@Override
	public void stateMachineStop() {
		cache.clear();
		return;
	}

	@Override
	public void stateMachineAbort() {
		cache.clear();
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
		return "JBPlayer"; // "Brian and Jeff'); DROP TABLE TEAMS; --";
	}
}
