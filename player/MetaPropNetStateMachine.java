import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.ggp.base.util.gdl.grammar.Gdl;
import org.ggp.base.util.gdl.grammar.GdlSentence;
import org.ggp.base.util.propnet.architecture.components.Proposition;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.prover.query.ProverQueryBuilder;

public abstract class MetaPropNetStateMachine extends StateMachine {

	private List<Role> roles;
	private Map<GdlSentence, Integer> inputmap;
	private Map<Role, List<Move>> legalPropositions;
	private List<Move> legals;
	
	public void init(List<Role> roles, Map<GdlSentence, Integer> inputmap,
			Map<Role, List<Move>> legalPropositions, List<Move> legals) {
		this.roles = roles;
		this.inputmap = inputmap;
		this.legalPropositions = legalPropositions;
		this.legals = legals;
	}
	
	public void initialize(List<Gdl> desc) {}

	@Override
	public List<Move> findActions(Role role) throws MoveDefinitionException {
		return legalPropositions.get(role);
	}

	@Override
	public int getGoal(MachineState state, Role role) throws GoalDefinitionException {
		return goal(((PropNetMachineState)state).props, roles.indexOf(role));
	}
	
	abstract int goal(boolean[] bases, int role);

	@Override
	public boolean isTerminal(MachineState state) {
		return terminal(((PropNetMachineState)state).props);
	}

	abstract boolean terminal(boolean[] bases);

	@Override
	public List<Role> getRoles() {
		return roles;
	}

	@Override
	public MachineState getInitialState() {
		return new PropNetMachineState(initial());
	}
	
	abstract boolean[] initial();

	@Override
	public List<Move> getLegalMoves(MachineState state, Role role) throws MoveDefinitionException {
		boolean[] result = legal(((PropNetMachineState)state).props);
		List<Move> legals = new ArrayList<Move>();
		for (int i = 0; i < result.length; i ++) {
			if (result[i] && legalPropositions.get(role).contains(this.legals.get(i))) {
				legals.add(this.legals.get(i));
			}
		}
		return legals;
	}
	
	abstract boolean[] legal(boolean[] bases);

	@Override
	public MachineState getNextState(MachineState state, List<Move> moves) throws TransitionDefinitionException {
		boolean[] inputs = new boolean[inputmap.values().size()];
		Map<Role, Integer> roleIndices = getRoleIndices();
		for (int i = 0; i < roles.size(); i++) {
			int index = roleIndices.get(roles.get(i));
			inputs[inputmap.get(ProverQueryBuilder.toDoes(roles.get(i), moves.get(index)))] = true;
		}
		return new PropNetMachineState(next(((PropNetMachineState)state).props, inputs));
	}

	abstract boolean[] next(boolean[] bases, boolean[] inputs);
}

class PropNetMachineState extends MachineState {
	boolean[] props;
	public PropNetMachineState(boolean[] props) {
		this.props = props;
	}
}