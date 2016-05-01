import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.ggp.base.player.gamer.exception.GamePreviewException;
import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.game.Game;
import org.ggp.base.util.gdl.grammar.GdlSentence;
import org.ggp.base.util.propnet.architecture.Component;
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
	BetterPropNetStateMachine prop;

	@Override
	public StateMachine getInitialStateMachine() {
		prover = new ProverStateMachine();
		prop = new BetterPropNetStateMachine();
		return prop;
	}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		// TODO Auto-generated method stub
		prover.initialize(prop.description);
		MachineState state = prover.getInitialState();
//		System.out.println(prop.getInitialState());
//		for (Component c : prop.propNet.getInitProposition().getOutputs())
//			System.out.println(c);
		if (!prop.getInitialState().equals(state)) {
			System.out.println("Prop1 Initial error.");
		}
		while (!prover.isTerminal(state)) {
			List<Move> moves = prover.getRandomJointMove(state);
			MachineState temp = state;
			state = prover.getNextState(state, moves);
			if (!prop.getNextState(temp, moves).equals(state)) {
				Set<GdlSentence> contents = new HashSet<GdlSentence>(prop.getNextState(temp, moves).getContents());
				Set<GdlSentence> newcontents = new HashSet<GdlSentence>(state.getContents());
				contents.removeAll(state.getContents());
				newcontents.removeAll(prop.getNextState(temp, moves).getContents());
				System.out.println(prop.getNextState(temp, moves).getContents().size());
				System.out.println(state.getContents().size());
				System.out.println("Prop: " + new MachineState(contents));
				System.out.println("Prover: " + new MachineState(newcontents));
			}
			System.out.println();
//			System.out.println(state);
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
