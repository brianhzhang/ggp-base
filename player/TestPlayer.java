import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.ggp.base.player.gamer.exception.GamePreviewException;
import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.game.Game;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.prover.ProverStateMachine;

public class TestPlayer extends StateMachineGamer {

	StateMachine prover;
	StateMachine prop;

	@Override
	public StateMachine getInitialStateMachine() {
		return new GDLGetter();
	}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		// TODO Auto-generated method stub
		// BetterMetaPropNetStateMachineFactory fac =
		// new BetterMetaPropNetStateMachineFactory(((GDLGetter)
		// getStateMachine()).getDescription());
		// LolAnotherMetaPropNetStateMachineFactory facb =
		// new LolAnotherMetaPropNetStateMachineFactory(((GDLGetter)
		// getStateMachine()).getDescription());
		Log.setFile(getMatch().getMatchId() + "_" + getRole());
		Log.println("");
		prover = new JustKiddingPropNetStateMachine();
		prop = new YeahWasntTheLastOnePropNetStateMachine();
		prover.initialize(((GDLGetter) getStateMachine()).getDescription());
		prop.initialize(((GDLGetter) getStateMachine()).getDescription());
		//		int total = 0;
		while (System.currentTimeMillis() < timeout - 3000) {
			MachineState state = prover.getInitialState();
			// System.out.println(prop.getInitialState());
			// for (Component c : prop.propNet.getInitProposition().getOutputs())
			// System.out.println(c);
			MachineState propstate = prop.getInitialState();
			// int countB = 0;
			// for (int i = 0; i < ((PropNetMachineState) propstate).props.length; i ++){
			// countB += ((PropNetMachineState) propstate).props[i] ? 1 : -1;
			// countB += ((PropNetMachineState) state).props[i] ? -1 : 1;
			// }
			// if (countB != 0) {
			// System.out.println("Prop1 Initial error.");
			// System.out.println("Prop: " + Arrays.toString(((PropNetMachineState)propstate).props));
			// System.out.println("Prover: " + Arrays.toString(((PropNetMachineState)state).props));
			// }
			while (!prover.isTerminal(state)) {
				//			total++;
				// if (total > 7) break;
				List<Move> moves = prover.getRandomJointMove(state);
				List<Move> legals = prover.getLegalMoves(state, getRole());
				List<Move> props = prop.getLegalMoves(propstate, getRole());
				if (!(new HashSet<>(props)).equals(new HashSet<>(legals))) {
					Set<Move> contents = new HashSet<Move>(props);
					Set<Move> newcontents = new HashSet<Move>(legals);
					System.out.print("Prop (Moves): [");
					for (Move m : contents) {
						System.out.print(m + ", ");
					}
					System.out.print("]\nProver (Moves): [");
					for (Move m : newcontents) {
						System.out.print(m + ", ");
					}
					System.out.println("]");
				}
				state = prover.getNextState(state, moves);
				propstate = prop.getNextState(propstate, moves);
				// int count = 0;
				// for (int i = 0; i < ((PropNetMachineState) propstate).props.length; i ++){
				// count += ((PropNetMachineState) propstate).props[i] ? 1 : -1;
				// count += ((PropNetMachineState) state).props[i] ? -1 : 1;
				// }
				// if (count != 0) {
				// System.out.println("Prop: " +
				// Arrays.toString(((PropNetMachineState)propstate).props));
				// System.out.println("Prover: " + Arrays.toString(((PropNetMachineState)state).props));
				// }
				// System.out.println(state);
			}
			if (!prop.isTerminal(propstate)) System.out.println("Fuck");
		}
	}

	@Override
	public Move stateMachineSelectMove(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		return null;
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
