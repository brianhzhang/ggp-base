import java.util.List;

import org.ggp.base.player.gamer.exception.GamePreviewException;
import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.game.Game;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.prover.ProverStateMachine;

public class TestPlayer extends StateMachineGamer {

	ProverStateMachine prover;
	PropNetStateMachine prop;
	PropNetStateMachine2 prop2;

	@Override
	public StateMachine getInitialStateMachine() {
		prover = new ProverStateMachine();
		prop2 = new PropNetStateMachine2();
		prop = new PropNetStateMachine();
		return prop;
	}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		// TODO Auto-generated method stub
		StateMachine machine = getStateMachine();
		MachineState state = machine.getInitialState();
		prover.initialize(prop.description);
		prop2.initialize(prop.description);
		if (!prop.getInitialState().equals(state)) {
			System.out.println("Prop1 Initial error.");
		}
		if (!prop2.getInitialState().equals(state)) {
			System.out.println("Prop2 Initial error.");
		}
		while (!machine.isTerminal(state)) {
			List<Move> moves = machine.getRandomJointMove(state);
			MachineState temp = state;
			state = machine.getNextState(state, moves);
			if (!prop.getNextState(temp, moves).equals(state)) {
				System.out.println("Prop1 error.");
			}
			if (!prop2.getNextState(temp, moves).equals(state)) {
				System.out.println("Prop2 error.");
			}
		}
	}

	@Override
	public Move stateMachineSelectMove(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		return getStateMachine().getLegalMoves(getCurrentState(), getRole()).get(0);
	}

	@Override
	public void stateMachineStop() {

	}

	@Override
	public void stateMachineAbort() {

	}

	@Override
	public void preview(Game g, long timeout) throws GamePreviewException {
		// TODO Auto-generated method stub

	}

	@Override
	public String getName() {
		return "Test";
	}

}
