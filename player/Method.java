import java.util.List;

import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;

public abstract class Method {
	
	public abstract void metaGame(long timeout);

	public abstract Move run(StateMachine machine, MachineState state, Role role, List<Move> moves, long timeout)
			throws GoalDefinitionException, MoveDefinitionException, TransitionDefinitionException;
	
	public abstract void cleanUp();
	
}
