import java.util.List;

import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;

public class Heuristic extends Method {

	public static final int TIMEOUT_SCORE = MyPlayer.MIN_SCORE - 1;

	private HeuristicFn[] heuristics = { this::mobility, this::focus, this::goal };
	private double[] weights = { 50, 0, 50 };
	private double[] exps = { 0.1, 1, 1 };

	@Override
	public void metaGame(StateMachineGamer gamer, long timeout) {
	}

	@Override
	public Move run(StateMachine machine, MachineState state, Role role, List<Move> moves,
			long timeout) throws GoalDefinitionException, MoveDefinitionException,
					TransitionDefinitionException {
		Move bestMove = moves.get(0);
		int bestScore = MyPlayer.MIN_SCORE;

		int level = 0;
		while (System.currentTimeMillis() < timeout) {
			level++;
			// alpha-beta heuristic: analyze previous best move first
			int score = minscore(machine, state, role, bestMove, MyPlayer.MIN_SCORE,
					MyPlayer.MAX_SCORE, level, timeout);
			if (score == TIMEOUT_SCORE) break;
			bestScore = score;
			for (Move move : moves) {
				if (move == bestMove) continue;
				score = minscore(machine, state, role, move, bestScore, MyPlayer.MAX_SCORE, level,
						timeout);
				if (score == TIMEOUT_SCORE) break;
				if (score > bestScore) {
					bestMove = move;
					bestScore = score;
					if (score == MyPlayer.MAX_SCORE) break;
				}
			}
		}
		System.out.printf("bestmove=%s score=%d depth=%d\n", bestMove, bestScore, level);
		return bestMove;
	}

	private int maxscore(StateMachine machine, MachineState state, Role role, int alpha, int beta,
			int level, long timeout) throws GoalDefinitionException, MoveDefinitionException,
					TransitionDefinitionException {
		if (machine.isTerminal(state)) return machine.findReward(role, state);
		if (level <= 0) return heuristic(role, state, machine);
		if (System.currentTimeMillis() > timeout) return TIMEOUT_SCORE;
		List<Move> actions = machine.findLegals(role, state);
		for (Move move : actions) {
			int score = minscore(machine, state, role, move, alpha, beta, level, timeout);
			if (score == TIMEOUT_SCORE) return score;
			alpha = Math.max(alpha, score);
			if (alpha >= beta) break;
		}
		return alpha;
	}

	// as seen in notes ch 6
	private int minscore(StateMachine machine, MachineState state, Role role, Move move, int alpha,
			int beta, int level, long timeout) throws GoalDefinitionException,
					MoveDefinitionException, TransitionDefinitionException {
		if (System.currentTimeMillis() > timeout) return TIMEOUT_SCORE;
		// use joint moves so that we can deal with n-player games; n != 2
		for (List<Move> jmove : machine.getLegalJointMoves(state, role, move)) {
			MachineState next = machine.getNextState(state, jmove);
			int score = maxscore(machine, next, role, alpha, beta, level - 1, timeout);
			if (score == TIMEOUT_SCORE) return score;
			beta = Math.min(beta, score);
			if (alpha >= beta) return alpha;
		}
		return beta;
	}

	@Override
	public void cleanUp() {

	}

	private int heuristic(Role role, MachineState state, StateMachine machine)
			throws MoveDefinitionException, GoalDefinitionException {
		double heuristic = 0;
		for (int i = 0; i < weights.length; i++) {
			heuristic += weights[i] * Math.pow(heuristics[i].eval(role, state, machine), exps[i]);
		}
		return (int) heuristic;
	}

	private double mobility(Role role, MachineState state, StateMachine machine) {
		try {
			List<Move> feasibles = machine.findActions(role);
			List<Move> actions = machine.findLegals(role, state);
			return 1.0 * actions.size() / feasibles.size();
		} catch (MoveDefinitionException e) {
			e.printStackTrace();
			return MyPlayer.MIN_SCORE;
		}
	}

	private double focus(Role role, MachineState state, StateMachine machine) {
		return 1 - mobility(role, state, machine);
	}

	private double goal(Role role, MachineState state, StateMachine machine) {
		try {
			return machine.findReward(role, state) / 100.;
		} catch (GoalDefinitionException e) {
			return MyPlayer.MIN_SCORE;
		}
	}
}

interface HeuristicFn {
	public double eval(Role role, MachineState state, StateMachine machine);
}
