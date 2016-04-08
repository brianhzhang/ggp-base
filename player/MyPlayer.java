import java.util.List;

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

	public final int MAX_SCORE = 100;
	public final int MIN_SCORE = 0;

	@Override
	public StateMachine getInitialStateMachine() {
		return new CachedStateMachine(new ProverStateMachine());
	}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {
		return;
	}

	@Override
	public Move stateMachineSelectMove(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {
		StateMachine machine = getStateMachine();
		MachineState state = getCurrentState();
		Role role = getRole();

		List<Move> moves = machine.findLegals(role, state);

		/** legal player **/
		// legal player #1: 8432
		// legal player #2: 1344
		// return moves.get(0);

		/** random player **/
		// random player #1: 6920
		// random player #2: 1344
		// Random random = new Random();
		// return moves.get(random.nextInt(moves.size())); // random player

		/** alpha beta player **/
		// alpha beta #1: 7234
		// alpha beta #2: 4325
		Move bestMove = moves.get(0);
		int bestScore = MIN_SCORE;
		for (Move move : moves) {
			int score = minscore(machine, state, role, move,
					MIN_SCORE, MAX_SCORE);
			if (score == MAX_SCORE) return move;
			if (score > bestScore) {
				bestMove = move;
				bestScore = score;
			}

		}
		return bestMove;
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

	@Override
	public void stateMachineStop() {
		return;
	}

	@Override
	public void stateMachineAbort() {
		return;
	}

	@Override
	public void preview(Game g, long timeout) throws GamePreviewException {
		return;
	}

	@Override
	public String getName() {
		return "Brian and Jeff'); DROP TABLE TEAMS; --";
	}

}
