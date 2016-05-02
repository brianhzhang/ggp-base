

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import org.ggp.base.util.gdl.grammar.Gdl;
import org.ggp.base.util.gdl.grammar.GdlConstant;
import org.ggp.base.util.gdl.grammar.GdlRelation;
import org.ggp.base.util.gdl.grammar.GdlSentence;
import org.ggp.base.util.propnet.architecture.Component;
import org.ggp.base.util.propnet.architecture.PropNet;
import org.ggp.base.util.propnet.architecture.components.Constant;
import org.ggp.base.util.propnet.architecture.components.Proposition;
import org.ggp.base.util.propnet.factory.OptimizingPropNetFactory;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.prover.query.ProverQueryBuilder;


import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.ggp.base.util.gdl.grammar.Gdl;
import org.ggp.base.util.gdl.grammar.GdlConstant;
import org.ggp.base.util.gdl.grammar.GdlRelation;
import org.ggp.base.util.gdl.grammar.GdlSentence;
import org.ggp.base.util.propnet.architecture.Component;
import org.ggp.base.util.propnet.architecture.PropNet;
import org.ggp.base.util.propnet.architecture.components.Proposition;
import org.ggp.base.util.propnet.factory.OptimizingPropNetFactory;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.prover.query.ProverQueryBuilder;

@SuppressWarnings("unused")
public class PropNetStateMachine extends StateMachine {
	/** The underlying proposition network */
	private PropNet propNet;
	/** The topological ordering of the propositions */
	private List<Proposition> ordering;
	/** The player roles */
	private List<Role> roles;
	
	public List<Gdl> description;

	/**
	 * Initializes the PropNetStateMachine. You should compute the topological ordering here.
	 * Additionally you may compute the initial state here, at your discretion.
	 */
	@Override
	public void initialize(List<Gdl> description) {
		try {
			propNet = OptimizingPropNetFactory.create(description);
			roles = propNet.getRoles();
			ordering = getOrdering();
			this.description = description;
		} catch (InterruptedException e) {
			throw new RuntimeException(e);
		}
	}

	/**
	 * Computes if the state is terminal. Should return the value of the terminal proposition for
	 * the state.
	 */
	@Override
	public boolean isTerminal(MachineState state) {
		markbases(state.getContents());
		markviews();
		return propNet.getTerminalProposition().getValue();
	}

	/**
	 * Computes the goal for a role in the current state. Should return the value of the goal
	 * proposition that is true for that role. If there is not exactly one goal proposition true for
	 * that role, then you should throw a GoalDefinitionException because the goal is ill-defined.
	 */
	@Override
	public int getGoal(MachineState state, Role role) throws GoalDefinitionException {
		markbases(state.getContents());
		markviews();
		Set<Proposition> bases = propNet.getGoalPropositions().get(role);
		for (Proposition p : bases) {
			if (p.getValue()) return Integer.parseInt(p.getName().get(1).toString());
		}
		throw new GoalDefinitionException(state, role);
	}

	/**
	 * Returns the initial state. The initial state can be computed by only setting the truth value
	 * of the INIT proposition to true, and then computing the resulting state.
	 */
	@Override
	public MachineState getInitialState() {
		clearpropnet();
		propNet.getInitProposition().setValue(true);
		Map<GdlSentence, Proposition> bases = propNet.getBasePropositions();
		Set<GdlSentence> nexts = new HashSet<GdlSentence>();
		for (GdlSentence s : bases.keySet()) {
			if (bases.get(s).getSingleInput().getValue()) nexts.add(s);
		}
		return new MachineState(nexts);
	}

	/**
	 * Computes all possible actions for role.
	 */
	@Override
	public List<Move> findActions(Role role) throws MoveDefinitionException {
		return propToMoves(propNet.getLegalPropositions().get(role), true);
	}

	private List<Move> propToMoves(Set<Proposition> set, boolean any) {

		List<Move> moves = new ArrayList<Move>(set.size());
		for (Proposition p : set) {
			if (any || p.getValue()) {
				moves.add(new Move(p.getName().get(1)));
				continue;
			}
		}
		return moves;
	}

	/**
	 * Computes the legal moves for role in state.
	 */
	@Override
	public List<Move> getLegalMoves(MachineState state, Role role) throws MoveDefinitionException {
		markbases(state.getContents());
		markviews();
		return propToMoves(propNet.getLegalPropositions().get(role), false);
	}

	/**
	 * Computes the next state given state and the list of moves.
	 */
	@Override
	public MachineState getNextState(MachineState state, List<Move> moves)
			throws TransitionDefinitionException {
		markbases(state.getContents());
		markactions(toDoes(moves));
		markviews();
		Map<GdlSentence, Proposition> bases = propNet.getBasePropositions();
		Set<GdlSentence> nexts = new HashSet<GdlSentence>();
		for (GdlSentence s : bases.keySet()) {
			boolean val = bases.get(s).getSingleInput().getValue();
			if (val) nexts.add(s);
		}
		return new MachineState(nexts);
	}

	/**
	 * This should compute the topological ordering of propositions. Each component is either a
	 * proposition, logical gate, or transition. Logical gates and transitions only have
	 * propositions as inputs.
	 *
	 * The base propositions and input propositions should always be exempt from this ordering.
	 *
	 * The base propositions values are set from the MachineState that operations are performed on
	 * and the input propositions are set from the Moves that operations are performed on as well
	 * (if any).
	 *
	 * @return The order in which the truth values of propositions need to be set.
	 */
	public List<Proposition> getOrdering() {
		// List to contain the topological ordering.
		List<Proposition> order = new LinkedList<Proposition>();

		// All of the components in the PropNet
		Set<Component> components = new HashSet<Component>(propNet.getComponents());

		// All of the propositions in the PropNet.
		Set<Proposition> propositions = new HashSet<Proposition>(propNet.getPropositions());
		Collection<Proposition> bases = propNet.getBasePropositions().values();
		Collection<Proposition> inputs = propNet.getInputPropositions().values();
		ArrayDeque<Component> nodep = new ArrayDeque<Component>();
		for (Component c : components) {
			if (c.getInputs().size() == 0 || bases.contains(c) || inputs.contains(c)) {
				nodep.add(c);
			}
		}
		while (!nodep.isEmpty()) {
			Component p = nodep.poll();
			components.remove(p);
			if (p instanceof Proposition && !bases.contains(p) && !inputs.contains(p)) {
				order.add((Proposition) p);
			}
			for (Component c : p.getOutputs()) {
				boolean add = true;
				for (Component comp : c.getInputs()) {
					if (components.contains(comp)) {
						add = false;
						break;
					}
				}
				if (add && components.contains(c)) {
					nodep.add(c);
				}
			}
		}
		return order;
	}

	private void findChildren(Component prop, Set<Proposition> children, Set<Component> toRemove) {
		if (prop instanceof Proposition) {
			children.add((Proposition)prop);
		} else {
			toRemove.add(prop);
			for (Component c : prop.getOutputs()) {
				findChildren(c, children, toRemove);
			}
		}
	}

	/* Already implemented for you */
	@Override
	public List<Role> getRoles() {
		return roles;
	}

	/* Helper methods */

	/**
	 * The Input propositions are indexed by (does ?player ?action).
	 *
	 * This translates a list of Moves (backed by a sentence that is simply ?action) into
	 * GdlSentences that can be used to get Propositions from inputPropositions. and accordingly set
	 * their values etc. This is a naive implementation when coupled with setting input values, feel
	 * free to change this for a more efficient implementation.
	 *
	 * @param moves
	 * @return
	 */
	private Set<GdlSentence> toDoes(List<Move> moves) {
		Set<GdlSentence> doeses = new HashSet<GdlSentence>(moves.size());
		Map<Role, Integer> roleIndices = getRoleIndices();

		for (int i = 0; i < roles.size(); i++) {
			int index = roleIndices.get(roles.get(i));
			doeses.add(ProverQueryBuilder.toDoes(roles.get(i), moves.get(index)));
		}
		return doeses;
	}

	/**
	 * Takes in a Legal Proposition and returns the appropriate corresponding Move
	 *
	 * @param p
	 * @return a PropNetMove
	 */
	public static Move getMoveFromProposition(Proposition p) {
		return new Move(p.getName().get(1));
	}

	/**
	 * Helper method for parsing the value of a goal proposition
	 *
	 * @param goalProposition
	 * @return the integer value of the goal proposition
	 */
	private int getGoalValue(Proposition goalProposition) {
		GdlRelation relation = (GdlRelation) goalProposition.getName();
		GdlConstant constant = (GdlConstant) relation.get(1);
		return Integer.parseInt(constant.toString());
	}

	/**
	 * A Naive implementation that computes a PropNetMachineState from the true BasePropositions.
	 * This is correct but slower than more advanced implementations You need not use this method!
	 *
	 * @return PropNetMachineState
	 */
	public MachineState getStateFromBase() {
		Set<GdlSentence> contents = new HashSet<GdlSentence>();
		for (Proposition p : propNet.getBasePropositions().values()) {
			p.setValue(p.getSingleInput().getValue());
			if (p.getValue()) {
				contents.add(p.getName());
			}

		}
		return new MachineState(contents);
	}

	private void markbases(Set<GdlSentence> markings) {
		clearpropnet();
		Map<GdlSentence, Proposition> props = propNet.getBasePropositions();
		for (GdlSentence s : props.keySet()) {
			props.get(s).setValue(markings.contains(s));
		}
	}

	private void markactions(Set<GdlSentence> list) {
		Map<GdlSentence, Proposition> props = propNet.getInputPropositions();
		for (GdlSentence s : props.keySet()) {
			props.get(s).setValue(list.contains(s));
		}
	}

	private void clearpropnet() {
		for (Proposition s : propNet.getPropositions()) {
			s.setValue(false);
		}
	}

	private void markviews() {
		for (Proposition p : ordering) {
			p.setValue(p.getValue());
		}
	}
}