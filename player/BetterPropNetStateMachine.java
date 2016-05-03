import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
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
import org.ggp.base.util.propnet.architecture.components.Not;
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
public class BetterPropNetStateMachine extends StateMachine {
	/** The underlying proposition network */
	public PropNet propNet;
	/** The player roles */
	private List<Role> roles;

	private Set<GdlSentence> lastBases;
	private Set<GdlSentence> lastInputs;
	public List<Gdl> description;
	private StateMachine[] machines;

	public BetterPropNetStateMachine(StateMachine[] stateMachines) {
		this.machines = stateMachines;
	}

	/**
	 * Initializes the PropNetStateMachine. You should compute the topological ordering here.
	 * Additionally you may compute the initial state here, at your discretion.
	 */
	@Override
	public void initialize(List<Gdl> description) {
		List<Thread> threads = new ArrayList<Thread>();
		MTI mti = new MTI(this, description);
		mti.start();
		threads.add(mti);
		for (StateMachine m : machines) {
			mti = new MTI((BetterPropNetStateMachine) m, description);
			mti.start();
			threads.add(mti);
		}
		for (int i = 0; i < threads.size(); i ++) {
			try {
				threads.get(i).join();
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
	}
	
	public void threadInitialize(List<Gdl> description) {
		try {
			this.description = description;
			propNet = OptimizingPropNetFactory.create(description);
			for (Component c : propNet.getComponents()) {
				c.crystalize();
			}
			roles = propNet.getRoles();
			lastBases = new HashSet<GdlSentence>();
			lastInputs = new HashSet<GdlSentence>();
			Collection<Proposition> bases = propNet.getBasePropositions().values();
			Collection<Proposition> inputs = propNet.getInputPropositions().values();
			for (Proposition p : propNet.getPropositions()) {
				if (bases.contains(p) || inputs.contains(p)) {
					p.base = true;
				}
			}
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
		propNet.getInitProposition().propogate(false);
		Map<GdlSentence, Proposition> bases = propNet.getBasePropositions();
		Set<GdlSentence> nexts = new HashSet<GdlSentence>();
		for (GdlSentence s : bases.keySet()) {
			if (bases.get(s).getSingleInputarr().getValue()) nexts.add(s);
		}
		MachineState initial = new MachineState(nexts);
		propNet.getInitProposition().setValue(false);
		propNet.getInitProposition().propogate(false);
		return initial;
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
		Map<GdlSentence, Proposition> bases = propNet.getBasePropositions();
		Set<GdlSentence> nexts = new HashSet<GdlSentence>();
		for (GdlSentence s : bases.keySet()) {
			if (bases.get(s).getSingleInputarr().getValue()) nexts.add(s);
		}
		return new MachineState(nexts);
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

	private void markbases(Set<GdlSentence> contents) {
		Set<GdlSentence> nowFalse = new HashSet<GdlSentence>(lastBases);
		Set<GdlSentence> nowTrue = new HashSet<GdlSentence>(contents);
		nowFalse.removeAll(contents);
		nowTrue.removeAll(lastBases);
		Map<GdlSentence, Proposition> bases = propNet.getBasePropositions();
		for (GdlSentence s : nowFalse) {
			bases.get(s).setValue(false);
			bases.get(s).startPropogate();
		}
		for (GdlSentence s : nowTrue) {
			bases.get(s).setValue(true);
			bases.get(s).startPropogate();
		}
		lastBases = contents;
	}

	private void markactions(Set<GdlSentence> does) {
		Set<GdlSentence> nowFalse = new HashSet<GdlSentence>(lastInputs);
		Set<GdlSentence> nowTrue = new HashSet<GdlSentence>(does);
		nowFalse.removeAll(does);
		nowTrue.removeAll(lastInputs);
		Map<GdlSentence, Proposition> bases = propNet.getInputPropositions();
		for (GdlSentence s : nowFalse) {
			bases.get(s).setValue(false);
			bases.get(s).startPropogate();
		}
		for (GdlSentence s : nowTrue) {
			bases.get(s).setValue(true);
			bases.get(s).startPropogate();
		}
		lastInputs = does;
	}

	private void clearpropnet() {
		Set<Component> nots = new HashSet<Component>();
		for (Component s : propNet.getComponents()) {
			s.reset();
			if (s instanceof Not) nots.add(s);
		}
		for (Component s : nots) {
			s.propogate(true);
		}
	}
}
//MTI = Multi Thread Initializer
class MTI extends Thread {
	BetterPropNetStateMachine p;
	List<Gdl> description;
	public MTI(BetterPropNetStateMachine p, List<Gdl> description) {
		this.p = p;
		this.description = description;
	}
	
	public void run() {
		p.threadInitialize(description);
	}
}