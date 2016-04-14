import java.util.List;

import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;

public class Heuristic extends Method {
	
	double mobilityWeight = 1;
	double focusWeight = 0;
	double goalWeight = 1;

	public void metaGame(long timeout) {}

	public Move run(StateMachine machine, MachineState state, Role role, List<Move> moves, long timeout)
			throws GoalDefinitionException, MoveDefinitionException, TransitionDefinitionException {
		Move bestMove = moves.get(0);
		int bestScore = MyPlayer.MIN_SCORE;
		int level = 0;
		while (System.currentTimeMillis() < timeout) { //just to prevent infinite loop
			level ++;
			for (Move move : moves) {
				int score = minscore(machine, state, role, move, bestScore, MyPlayer.MAX_SCORE, level, timeout);
				if (score == MyPlayer.MIN_SCORE - 1) break;
				if (score > bestScore) {
					bestMove = move;
					bestScore = score;
					if (score == MyPlayer.MAX_SCORE) break;
				}
			}
		}
		System.out.printf("bestmove=%s score=%d\n", bestMove, bestScore);
		return bestMove;
	}

	private int maxscore(StateMachine machine, MachineState state, Role role, int alpha, int beta, int level, long timeout)
			throws GoalDefinitionException, MoveDefinitionException, TransitionDefinitionException {
		if (machine.isTerminal(state)) return machine.findReward(role, state);
		if (level <= 0) return heuristic(role, state, machine);
		if (System.currentTimeMillis() > timeout) return MyPlayer.MIN_SCORE - 1;
		List<Move> actions = machine.findLegals(role, state);
		for (Move move : actions) {
			int score = minscore(machine, state, role, move, alpha, beta, level, timeout);
			if (score == MyPlayer.MIN_SCORE - 1) return score;
			alpha = Math.max(alpha, score);
			if (alpha >= beta) break;
		}
		return alpha;
	}

	// as seen in notes ch 6
	private int minscore(StateMachine machine, MachineState state, Role role, Move move, int alpha,
			int beta, int level, long timeout)
					throws GoalDefinitionException, MoveDefinitionException, TransitionDefinitionException {
		if (System.currentTimeMillis() > timeout) return MyPlayer.MIN_SCORE - 1;
		// use joint moves so that we can deal with n-player games; n != 2
		for (List<Move> jmove : machine.getLegalJointMoves(state, role, move)) {
			MachineState next = machine.getNextState(state, jmove);
			int score = maxscore(machine, next, role, alpha, beta, level - 1, timeout);
			if (score == MyPlayer.MIN_SCORE - 1) return score;
			beta = Math.min(beta, score);
			if (alpha >= beta) return alpha;
		}
		return beta;
	}

	public void cleanUp() {

	}

	private int heuristic(Role role, MachineState state, StateMachine machine) {
		try {
			return (int) ((mobilityWeight * mobility(role, state, machine) + 
					focusWeight * focus(role, state, machine) +
					goalWeight * machine.findReward(role, state)) / (goalWeight + focusWeight + mobilityWeight));
		} catch (GoalDefinitionException e) {}
		return (int) ((mobilityWeight * mobility(role, state, machine) + 
				focusWeight * focus(role, state, machine)) / (focusWeight + mobilityWeight));
	}

	private double mobility(Role role, MachineState state, StateMachine machine) {
		List<Move> actions;
		List<Move> feasibles;
		try {
			feasibles = machine.findActions(role);
			actions = machine.findLegals(role,state);
			return (actions.size()/feasibles.size() * 100);
		} catch (MoveDefinitionException e) {
			e.printStackTrace();
		}
		return 0;
	}

	private double focus(Role role, MachineState state, StateMachine machine) {
		List<Move> actions;
		List<Move> feasibles;
		try {
			feasibles = machine.findActions(role);
			actions = machine.findLegals(role,state);
			return (actions.size()/feasibles.size() * 100);
		} catch (MoveDefinitionException e) {
			e.printStackTrace();
		}
		return 0;
	}

}

