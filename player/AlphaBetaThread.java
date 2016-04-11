import java.util.List;
import java.util.concurrent.BlockingQueue;

import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;

public class AlphaBetaThread extends Thread {

	BlockingQueue<Work> work;
	StateMachine machine;
	Role role;
	BestMove best;

	public AlphaBetaThread(BlockingQueue<Work> q, StateMachine m, Role r, BestMove b) {
		work = q;
		machine = m;
		role = r;
		best = b;
	}

	@Override
	public void run() {
		while (!work.isEmpty()) {
			Work move = work.poll();
			if (move == null) break;
			int score = MyPlayer.MIN_SCORE;
			try {
				if (move.max) {
					score = maxscore(machine, move.state, role, move.original.alpha, move.original.beta);
//					move.original.beta = Math.min(move.original.beta, score);
				} else {
					score = minscore(machine, move.state, role, move.m, move.original.alpha, move.original.beta);
//					move.original.alpha = Math.max(move.original.alpha, score);
				}
			} catch (GoalDefinitionException | MoveDefinitionException | TransitionDefinitionException e) {
				e.printStackTrace();
			}
			if (score == MyPlayer.MAX_SCORE) {
				best.m = move.original.m;
				best.score = score;
				work.clear();
			}
			if (score > best.score) {
				best.m = move.original.m;
				best.score = score;
			}
		}
	}

	// as seen in notes ch. 6
	private int maxscore(StateMachine machine, MachineState state, Role role,
			int alpha, int beta)
					throws GoalDefinitionException,
					MoveDefinitionException, TransitionDefinitionException {
		if (machine.isTerminal(state)) return machine.findReward(role, state);
		List<Move> actions = machine.findLegals(role, state);
		for (Move move : actions) {
			int score = minscore(machine, state, role, move, alpha, beta);
			alpha = Math.max(alpha, score);
			if (alpha >= beta) return beta;
		}
		return alpha;
	}

	// as seen in notes ch 6
	private int minscore(StateMachine machine, MachineState state, Role role,
			Move move, int alpha, int beta)
					throws GoalDefinitionException,
					MoveDefinitionException, TransitionDefinitionException {
		// use joint moves so that we can deal with n-player games; n != 2
		for (List<Move> jmove : machine.getLegalJointMoves(state, role, move)) {
			MachineState next = machine.getNextState(state, jmove);
			int score = maxscore(machine, next, role, alpha, beta);
			beta = Math.min(beta, score);
			if (alpha >= beta) return alpha;
		}
		return beta;
	}

}

class BestMove {
	public Move m;
	public int score = MyPlayer.MIN_SCORE;
}

class Work {
	public FirstMove original;
	public Move m;
	public MachineState state;
	public boolean max;
}

class FirstMove {
	public Move m;
	public int alpha;
	public int beta;
}
