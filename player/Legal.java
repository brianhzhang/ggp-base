import java.util.List;

import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;

public class Legal extends Method {

	@Override
	public void metaGame(StateMachineGamer gamer, long timeout) {
	}

	@Override
	public Move run(StateMachine machine, MachineState state, Role role, List<Move> moves,
			long timeout) throws GoalDefinitionException, MoveDefinitionException,
					TransitionDefinitionException {
		return moves.get(0);
	}

	@Override
	public void cleanUp() {
	}

}
