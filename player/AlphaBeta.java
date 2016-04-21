import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;

public class AlphaBeta extends Method {

	public Map<MachineState, Bound> cache = new HashMap<MachineState, Bound>();

	public int stats_nnodes = 0;
	public int stats_ncachehits = 0;

	@Override
	public void metaGame(StateMachineGamer gamer, long timeout) {
	}

	@Override
	public Move run(StateMachine machine, MachineState state, Role role, List<Move> moves,
			long timeout) throws GoalDefinitionException, MoveDefinitionException,
					TransitionDefinitionException {
		stats_nnodes = 0;
		stats_ncachehits = 0;
		Move bestMove = moves.get(0);
		int bestScore = MyPlayer.MIN_SCORE;
		for (Move move : moves) {
			int score = minscore(machine, state, role, move, bestScore, MyPlayer.MAX_SCORE);
			if (score > bestScore) {
				bestMove = move;
				bestScore = score;
				if (score == MyPlayer.MAX_SCORE) break;
			}
		}
		Log.printf("time=%d bestmove=%s score=%d nodes=%d cachehits=%d cachesize=%d\n",
				timeout - System.currentTimeMillis(), bestMove, bestScore, stats_nnodes,
				stats_ncachehits, cache.size());
		return bestMove;
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
	public void cleanUp() {
		cache.clear();
	}

}

class Bound {
	int lower = MyPlayer.MIN_SCORE;
	int upper = MyPlayer.MAX_SCORE;
}
