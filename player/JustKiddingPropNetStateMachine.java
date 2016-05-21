import java.io.Serializable;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import org.ggp.base.util.gdl.grammar.Gdl;
import org.ggp.base.util.gdl.grammar.GdlConstant;
import org.ggp.base.util.gdl.grammar.GdlRelation;
import org.ggp.base.util.propnet.architecture.Component;
import org.ggp.base.util.propnet.architecture.PropNet;
import org.ggp.base.util.propnet.architecture.components.And;
import org.ggp.base.util.propnet.architecture.components.Constant;
import org.ggp.base.util.propnet.architecture.components.Not;
import org.ggp.base.util.propnet.architecture.components.Or;
import org.ggp.base.util.propnet.architecture.components.Proposition;
import org.ggp.base.util.propnet.architecture.components.Transition;
import org.ggp.base.util.propnet.factory.OptimizingPropNetFactory;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;

public class JustKiddingPropNetStateMachine extends StateMachine {

	int[] comps;
	int[] initcomps;
	int[][] structure;
	List<Role> roles;
	Map<Role, List<Move>> actions;
	int term;
	int init;
	int[] basearr;
	int[] inputarr;
	Map<RoleMove, Integer> inputmap;
	Move[] legals;
	int[][] legalarr;
	int[][] goals;
	PropNetMachineState last;
	int[] legaltoinput;
	Random rgen = new Random();
	long x = System.nanoTime();

	PropNet p;
	ArrayList<Proposition> props;

	class RoleMove implements Serializable {
		private static final long serialVersionUID = 1L;
		Move m;
		int role;

		RoleMove(Move m, int role) {
			this.m = m;
			this.role = role;
		}

		@Override
		public boolean equals(Object o) {
			if ((o != null) && (o instanceof RoleMove)) {
				RoleMove move = (RoleMove) o;
				return move.m.equals(m) && move.role == role;
			}

			return false;
		}

		@Override
		public int hashCode() {
			return m.hashCode() + role;
		}
	}

	@Override
	public void initialize(List<Gdl> description) {
		p = null;
		try {
			p = OptimizingPropNetFactory.create(description);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}

		List<Component> components = new ArrayList<Component>(p.getComponents());
		List<Component> legaltoinputhelper = new ArrayList<Component>();
		for (Component c : components) {
			c.crystalize();
		}
		props = new ArrayList<Proposition>();
		comps = new int[components.size() * 2];
		structure = new int[components.size()][];
		roles = p.getRoles();
		actions = new HashMap<Role, List<Move>>();
		basearr = new int[p.getBasePropositions().values().size()];
		inputarr = new int[p.getInputPropositions().values().size()];
		inputmap = new HashMap<RoleMove, Integer>();
		int count = 0;
		int goalcount = 0;
		for (Role r : roles) {
			count += p.getLegalPropositions().get(r).size();
			goalcount += p.getGoalPropositions().get(r).size();
		}
		goals = new int[goalcount][3];
		legalarr = new int[count][2];
		legals = new Move[count];

		for (Role r : roles) {
			actions.put(r, propToMoves(p.getLegalPropositions().get(r)));
		}

		int base = 0;
		int input = 0;
		int legal = 0;
		int goal = 0;
		// Fill the components array
		for (int i = 0; i < components.size() * 2; i += 2) {
			if (p.getBasePropositions().values().contains(components.get(i / 2))) {
				comps[i] = 0;
				comps[i + 1] = components.indexOf(components.get(i / 2).getSingleInput()) * 2;
				basearr[base] = i;
				props.add((Proposition) components.get(i / 2));
				base++;
			} else if (p.getInputPropositions().values().contains(components.get(i / 2))) {
				comps[i] = 0;
				comps[i + 1] = 0;
				inputarr[input] = i;
				for (Role r : roles) {
					if (p.getLegalPropositions().get(r)
							.contains(p.getLegalInputMap().get(components.get(i / 2)))) {
						inputmap.put(new RoleMove(
								new Move(((Proposition) components.get(i / 2)).getName().get(1)),
								roles.indexOf(r)), input);
					}
				}
				input++;
			} else if (components.get(i / 2) instanceof Proposition) {
				boolean isView = true;
				for (Role r : roles) {
					if (p.getGoalPropositions().get(r).contains(components.get(i / 2))) {
						comps[i] = 0;
						comps[i + 1] = components.indexOf(components.get(i / 2).getSingleInput())
								* 2;
						goals[goal][0] = components.indexOf(components.get(i / 2).getSingleInput())
								* 2;
						goals[goal][1] = roles.indexOf(r);
						goals[goal][2] = getGoalValue((Proposition) components.get(i / 2));
						goal++;
						isView = false;
						break;
					}
					if (p.getLegalPropositions().get(r).contains(components.get(i / 2))) {
						comps[i] = 0x7FFFFFFF;
						comps[i + 1] = -1;
						legaltoinputhelper.add(p.getLegalInputMap().get(components.get(i / 2)));
						legalarr[legal][0] = components
								.indexOf(components.get(i / 2).getSingleInput()) * 2;
						legalarr[legal][1] = roles.indexOf(r);
						legals[legal] = new Move(
								((Proposition) components.get(i / 2)).getName().get(1));
						legal++;
						isView = false;
						break;
					}
				}
				if (p.getTerminalProposition().equals(components.get(i / 2))) {
					comps[i] = 0x7FFFFFFF;
					comps[i + 1] = components.indexOf(components.get(i / 2).getSingleInput()) * 2;
					term = i;
				} else if (p.getInitProposition().equals(components.get(i / 2))) {
					comps[i] = 0;
					comps[i + 1] = -1;
					init = i;
				} else if (isView) {
					comps[i] = 0x7FFFFFFF;
					comps[i + 1] = -1;
				}
			} else { // Component
				comps[i] = getComp(components.get(i / 2));
				comps[i + 1] = -1;
			}

			// fill the structure array:
			structure[i / 2] = new int[components.get(i / 2).getOutputs().size()];
			for (int j = 0; j < structure[i / 2].length; j++) {
				structure[i / 2][j] = components.indexOf(components.get(i / 2).getOutputarr()[j])
						* 2;
			}
		}

		legaltoinput = new int[input];
		for (int i = 0; i < legaltoinputhelper.size(); i++) {
			for (int j = 0; j < inputarr.length; j++) {
				if (components.get(inputarr[j] / 2) == legaltoinputhelper.get(i)) {
					legaltoinput[i] = j;
					break;
				}
			}
		}

		Set<Component> visited = new HashSet<Component>();

		for (int i = 0; i < basearr.length; i++) {
			for (int j = 0; j < structure[basearr[i] / 2].length; j++) {
				startPropagate(structure[basearr[i] / 2][j], 0, components, visited);
			}
		}
		for (int i = 0; i < inputarr.length; i++) {
			for (int j = 0; j < structure[inputarr[i] / 2].length; j++) {
				startPropagate(structure[inputarr[i] / 2][j], 0, components, visited);
			}
		}
		for (Component c : components) {
			if (c instanceof Constant) {
				startPropagate(components.indexOf(c) * 2, 0, components, visited);
			}
		}

		initcomps = comps.clone();
	}

	private int getComp(Component c) {
		if (c instanceof And) {
			return 0x80000000 - c.getInputs().size();
		} else if (c instanceof Or) {
			return 0x7FFFFFFF;
		} else if (c instanceof Not) {
			return 0xFFFFFFFF;
		} else if (c instanceof Transition) {
			return 0x7FFFFFFF;
		} else if (c instanceof Constant) {
			return (c.getValue()) ? 0xF0000000 : 0x0F000000;
		}
		return 0x1337420;
	}

	private List<Move> propToMoves(Set<Proposition> set) {
		List<Move> moves = new ArrayList<Move>(set.size());
		for (Proposition p : set) {
			moves.add(new Move(p.getName().get(1)));
		}
		return moves;
	}

	private int getGoalValue(Proposition goalProposition) {
		GdlRelation relation = (GdlRelation) goalProposition.getName();
		GdlConstant constant = (GdlConstant) relation.get(1);
		return Integer.parseInt(constant.toString());
	}

	@Override
	public List<Move> findActions(Role role) throws MoveDefinitionException {
		return actions.get(role);
	}

	@Override
	public int getGoal(MachineState state, Role role) throws GoalDefinitionException {
		markbases((PropNetMachineState) state);
		for (int i = 0; i < goals.length; i++) {
			if (((comps[goals[i][0]] >> 31) & 1) == 1 && roles.indexOf(role) == goals[i][1]) {
				return goals[i][2];
			}
		}
		return -1;
	}

	@Override
	public boolean isTerminal(MachineState state) {
		markbases((PropNetMachineState) state);
		return ((comps[comps[term + 1]] >> 31) & 1) == 1;
	}

	@Override
	public List<Role> getRoles() {
		return roles;
	}

	@Override
	public MachineState getInitialState() {
		comps = initcomps.clone();
		for (int i = 0; i < structure[init / 2].length; i++) {
			comps[init] = 0xF0000000;
			propagate(structure[init / 2][i], 1);
		}
		boolean[] next = new boolean[basearr.length];
		for (int i = 0; i < basearr.length; i++) {
			next[i] = (((comps[comps[basearr[i] + 1]] >> 31) & 1) == 1);
		}
		for (int i = 0; i < structure[init / 2].length; i++) {
			comps[init] = 0x0;
			propagate(structure[init / 2][i], -1);
		}
		return new PropNetMachineState(next);
	}

	@Override
	public List<Move> getLegalMoves(MachineState state, Role role) throws MoveDefinitionException {
		markbases((PropNetMachineState) state);
		ArrayList<Move> moves = new ArrayList<Move>();
		for (int i = 0; i < legals.length; i++) {
			if (((comps[legalarr[i][0]] >> 31) & 1) == 1 && legalarr[i][1] == roles.indexOf(role)) {
				moves.add(legals[i]);
			}
		}
		return moves;
	}

	@Override
	public MachineState getNextState(MachineState state, List<Move> moves)
			throws TransitionDefinitionException {
		markbases((PropNetMachineState) state);
		boolean[] inputs = new boolean[inputarr.length];
		for (int i = 0; i < moves.size(); i++) {
			if (moves.get(i) == null) continue;
			inputs[inputmap.get(new RoleMove(moves.get(i), i))] = true;
		}
		markinputs(inputs);
		boolean[] next = new boolean[basearr.length];
		for (int i = 0; i < basearr.length; i++) {
			next[i] = (((comps[comps[basearr[i] + 1]] >> 31) & 1) == 1);
		}
		return new PropNetMachineState(next);
	}

	private void markbases(PropNetMachineState state) {
		if (state == last) return;
		last = state;
		for (int i = 0; i < state.props.length; i++) {
			if (state.props[i] != (((comps[basearr[i]] >> 31) & 1) == 1)) {
				comps[basearr[i]] = state.props[i] ? 0xF0000000 : 0x0F000000;
				for (int j = 0; j < structure[basearr[i] / 2].length; j++) {
					propagate(structure[basearr[i] / 2][j], state.props[i] ? 1 : -1);
				}
			}
		}
	}

	private void markinputs(boolean[] inputs) {
		for (int i = 0; i < inputs.length; i++) {
			if (inputs[i] != (((comps[inputarr[i]] >> 31) & 1) == 1)) {
				comps[inputarr[i]] = inputs[i] ? 0xF0000000 : 0x0F000000;
				for (int j = 0; j < structure[inputarr[i] / 2].length; j++) {
					propagate(structure[inputarr[i] / 2][j], inputs[i] ? 1 : -1);
				}
			}
		}
	}

	private void propagate(int index, int newValue) {
		if (comps[index + 1] == -1) {
			int old = ((comps[index] >> 31) & 1);
			comps[index] += newValue;
			if (old != ((comps[index] >> 31) & 1)) {
				old = ((comps[index] >> 31) & 1) - old;
				for (int i = 0; i < structure[index / 2].length; i++) {
					propagate(structure[index / 2][i], old);
				}
			}
		}
	}

	// real index of the thing * 2 is index.
	private void startPropagate(int index, int newValue, List<Component> components,
			Set<Component> visited) {
		if (comps[index + 1] != -1) {
			return;
		}
		int old = ((comps[index] >> 31) & 1);
		comps[index] += newValue;
		if (old != ((comps[index] >> 31) & 1)
				|| (newValue == 0 && (old == 0 || !visited.contains(components.get(index / 2))))) {
			visited.add(components.get(index / 2));
			for (int i = 0; i < structure[index / 2].length; i++) {
				startPropagate(structure[index / 2][i], ((comps[index] >> 31) & 1), components,
						visited);
			}
		}
	}

	/* ########################################################################################## */

	public int[] internalDC(PropNetMachineState MS) {
		last = null;
		int[] moves = new int[roles.size()];
		int[] counts = new int[roles.size()];
		int[] indicies = new int[roles.size()];
		boolean[] state = MS.props.clone();
		while (!internalTerminal(state)) {
			internalRandomNextState(moves, counts, indicies, state);
		}

		// Get all of the goals for the terminal state.
		int[] goals = new int[roles.size()];
		for (int i = 0; i < goals.length; i++) {
			goals[i] = internalGoal(i);
		}
		return goals;
	}

	private int internalGoal(int role) {
		for (int i = 0; i < goals.length; i++) {
			if (((comps[goals[i][0]] >> 31) & 1) == 1 && role == goals[i][1]) {
				return goals[i][2];
			}
		}
		return -1;
	}

	private void internalRandomNextState(int[] moves, int[] counts, int[] indicies,
			boolean[] state) {
		internalRandomJoint(moves, counts, indicies);
		internalNextState(moves, state);
	}

	public int[] internalRandomJoint(int[] moves, int[] counts, int[] indicies) {
		for (int i = 0; i < moves.length; i++) {
			counts[i] = 0;
			indicies[i] = 0;
		}
		for (int i = 0; i < legals.length; i++) {
			if (((comps[legalarr[i][0]] >> 31) & 1) == 1) {
				counts[legalarr[i][1]]++;
				int random = (int) randomLong(counts[legalarr[i][1]]);
				if (random == 0) indicies[legalarr[i][1]] = i;
			}
		}
		for (int i = 0; i < indicies.length; i++) {
			moves[i] = legaltoinput[indicies[i]];
		}
		return moves;
	}

	public boolean[] internalNextState(int[] moves, boolean[] state) {
		boolean[] inputs = new boolean[inputarr.length];
		for (int i = 0; i < moves.length; i++) {
			inputs[moves[i]] = true;
		}
		markinputs(inputs);
		for (int i = 0; i < basearr.length; i++) {
			state[i] = (((comps[comps[basearr[i] + 1]] >> 31) & 1) == 1);
		}
		return state;
	}

	public boolean internalTerminal(boolean[] state) {
		internalMarkbases(state);
		return ((comps[comps[term + 1]] >> 31) & 1) == 1;
	}

	private void internalMarkbases(boolean[] bases) {
		for (int i = 0; i < bases.length; i++) {
			if (bases[i] != (((comps[basearr[i]] >> 31) & 1) == 1)) {
				comps[basearr[i]] = bases[i] ? 0xF0000000 : 0x0F000000;
				for (int j = 0; j < structure[basearr[i] / 2].length; j++) {
					propagate(structure[basearr[i] / 2][j], bases[i] ? 1 : -1);
				}
			}
		}
	}

	public long randomLong(int max) {
		x ^= (x << 21);
		x ^= (x >>> 35);
		x ^= (x << 4);
		return x % max;
	}
}
