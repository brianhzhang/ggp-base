import java.util.List;
import java.util.Random;

import org.ggp.base.player.gamer.exception.GamePreviewException;
import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.game.Game;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.cache.CachedStateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.prover.ProverStateMachine;

public class MyPlayer extends StateMachineGamer {

	private final Random random = new Random();

	public StateMachine getInitialStateMachine() {
		return new CachedStateMachine(new ProverStateMachine());
	}

	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {
		return;
	}

	public Move stateMachineSelectMove(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {
		List<Move> moves = getStateMachine().findLegals(getRole(),
				getCurrentState());
		// legal player #1: 8432
		// legal player #2: 1344
		return moves.get(0); // legal player
		// return moves.get(random.nextInt(moves.size())); // random player

	}

	public void stateMachineStop() {
		return;
	}

	public void stateMachineAbort() {
		return;
	}

	public void preview(Game g, long timeout) throws GamePreviewException {
		return;
	}

	public String getName() {
		return "Brian and Jeff'); DROP TABLE TEAMS; --";
	}

}
