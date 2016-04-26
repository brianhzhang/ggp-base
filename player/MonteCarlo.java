import java.util.List;

import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;

public class MonteCarlo extends Method {

	private static final int TIMEOUT_SCORE = MyPlayer.MIN_SCORE - 1;
	private static final int FAIL = MyPlayer.MIN_SCORE - 2;
	private static final int N_CHARGES = 10;
	
	private int charges = 0;
	private boolean searchUsed;
	
	@Override
	public void metaGame(StateMachineGamer gamer, long timeout) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public Move run(StateMachine machine, MachineState state, Role role, List<Move> moves, long timeout)
			throws GoalDefinitionException, MoveDefinitionException, TransitionDefinitionException {
		Log.println("--------------------");

		Move bestMove = moves.get(0);
		int bestScore = MyPlayer.MIN_SCORE;

		int level = 0;
		charges = 0;
		int startLevel = level;
		while (System.currentTimeMillis() < timeout) {
			searchUsed = false;
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
			if (!searchUsed && startLevel != level) break; // game fully analyzed
			Log.printf("bestmove=%s score=%d depth=%d charges=%d\n",
					bestMove, bestScore, level, charges);
			level++;
		}
		Log.printf("played=%s score=%d depth=%d charges=%d\n", bestMove,
				bestScore, level, charges);
		return bestMove;
	}

	@Override
	public void cleanUp() {
		// TODO Auto-generated method stub
		
	}
	
	private int maxscore(StateMachine machine, MachineState state, Role role, int alpha, int beta,
			int level, long timeout) throws GoalDefinitionException, MoveDefinitionException,
					TransitionDefinitionException {
		if (System.currentTimeMillis() > timeout) return TIMEOUT_SCORE;
		if (machine.isTerminal(state)) return machine.findReward(role, state);
		List<Move> actions = machine.findLegals(role, state);
		if (level <= 0) {
			int heuristic = monteCarlo(machine, state, role, timeout);
			return heuristic;
		}
		int a = alpha;
		for (Move move : actions) {
			int score = minscore(machine, state, role, move, a, beta, level, timeout);
			if (score == TIMEOUT_SCORE) return score;
			a = Math.max(a, score);
			if (a >= beta) break;
		}
		return a;
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
	
	private int monteCarlo(StateMachine machine, MachineState state, Role role, long timeout) {
		searchUsed = true;
		int score = 0;
		for (int i = 0; i < N_CHARGES; i ++) {
			charges ++;
			int newScore = FAIL;
			try {
				newScore = randomGame(machine, state, role, timeout);
			} catch (MoveDefinitionException | GoalDefinitionException | TransitionDefinitionException e) {
				e.printStackTrace();
			}
			if (newScore == FAIL || newScore == TIMEOUT_SCORE) {
				return TIMEOUT_SCORE;
			}
			score += newScore;
		}
		return score / N_CHARGES;
	}
	
	private int randomGame(StateMachine machine, MachineState state, Role role, long timeout)
			throws MoveDefinitionException, GoalDefinitionException, TransitionDefinitionException {
		while (!machine.isTerminal(state)) {
			if (System.currentTimeMillis() > timeout) return TIMEOUT_SCORE;
			state = machine.getRandomNextState(state);
		}
		return machine.findReward(role, state);
	}

}
