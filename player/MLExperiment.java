import java.util.*;

import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;

import jep.Jep;
import jep.JepException;

public class MLExperiment extends Method {

	YeahWasntTheLastOnePropNetStateMachine machine;
	Jep jep;
	boolean usingJep = true;
	
	MyPlayer gamer;
	int[] modelShape = {150, 150, 150};
	Object model;

	@Override
	public void metaGame(StateMachineGamer gamer, long timeout) {
		this.gamer = (MyPlayer) gamer;
		machine = new YeahWasntTheLastOnePropNetStateMachine();
		machine.initialize(this.gamer.gameDescription);
		Log.println("propnets initialized");
		try {
			jep = new Jep(false);
			jep.runScript("player/MLTest.py");
			model = jep.invoke("make", machine.p.getBasePropositions().size(), modelShape);
			Log.println("machine learning model initialized");
		} catch (JepException e) {
			Log.println("python unable to be initialized");
			usingJep = false;
		}
		int count = 0;
		Log.println("begin random exploration");
		PropNetMachineState init = (PropNetMachineState) machine.getInitialState();
		while (timeout - System.currentTimeMillis() > MyPlayer.TIMEOUT_BUFFER) {
			try {
				trainOnce(init);
			} catch (TransitionDefinitionException | MoveDefinitionException | GoalDefinitionException e) {
				e.printStackTrace();
			}
			count ++;
		}
		Log.println(count + " games explored");
	}
	
	private void trainOnce(PropNetMachineState current)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		ArrayList<boolean[]> states = new ArrayList<boolean[]>();
		while (!machine.isTerminal(current)) {
			current = (PropNetMachineState) machine.getNextState(current, machine.getRandomJointMove(current));
			states.add(current.props);
		}
		double result = machine.getGoal(current, gamer.getRole());
		boolean[][] data = new boolean[states.size()][states.get(0).length];
		data = states.toArray(data);
		try {
			jep.invoke("train", data, result, model);
		} catch (JepException e) {
			e.printStackTrace();
		}
	}

	@Override
	public Move run(StateMachine machine, MachineState state, Role role, List<Move> moves, long timeout)
			throws GoalDefinitionException, MoveDefinitionException, TransitionDefinitionException {
		return machine.getRandomMove(state, role);
	}

	@Override
	public void cleanUp() {
		// TODO Auto-generated method stub
		
	}
}