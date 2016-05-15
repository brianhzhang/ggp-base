import java.io.Serializable;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
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
		public boolean equals(Object o)
		{
			if ((o != null) && (o instanceof RoleMove)) {
				RoleMove move = (RoleMove) o;
				return move.m.equals(m) && move.role == role;
			}

			return false;
		}

		@Override
		public int hashCode()
		{
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

//		List<Component> components = getOrdering(new HashSet<Component>(p.getComponents()));
		List<Component> components = new ArrayList<Component>(p.getComponents());
		optimizePropNet(components, p);
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
		//Fill the components array
		for (int i = 0; i < components.size() * 2; i += 2) {
			if (p.getBasePropositions().values().contains(components.get(i/2))) {
				comps[i] = 0;
				comps[i + 1] = components.indexOf(components.get(i/2).getSingleInput()) * 2;
				basearr[base] = i;
				props.add((Proposition) components.get(i/2));
				base ++;
			} else if (p.getInputPropositions().values().contains(components.get(i/2))) {
				comps[i] = 0;
				comps[i + 1] = 0;
				inputarr[input] = i;
				for (Role r : roles) {
					if (p.getLegalPropositions().get(r).contains(p.getLegalInputMap().get(components.get(i/2)))) {
						inputmap.put(new RoleMove(new Move(((Proposition) components.get(i/2)).getName().get(1)),
								roles.indexOf(r)), input);
					}
				}
				input ++;
			} else if (components.get(i/2) instanceof Proposition) {
				boolean isView = true;
				for (Role r : roles) {
					if (p.getGoalPropositions().get(r).contains(components.get(i/2))) {
						comps[i] = 0;
						comps[i + 1] = components.indexOf(components.get(i/2).getSingleInput()) * 2;
						goals[goal][0] = components.indexOf(components.get(i/2).getSingleInput()) * 2;
						goals[goal][1] = roles.indexOf(r);
						goals[goal][2] = getGoalValue((Proposition) components.get(i/2));
						goal ++;
						isView = false;
						break;
					}
					if (p.getLegalPropositions().get(r).contains(components.get(i/2))) {
						comps[i] = 0;
						comps[i + 1] = components.indexOf(components.get(i/2).getSingleInput()) * 2;
						legalarr[legal][0] = i;
						legalarr[legal][1] = roles.indexOf(r);
						legals[legal] = new Move(((Proposition) components.get(i/2)).getName().get(1));
						legal ++;
						isView = false;
						break;
					}
				}
				if (p.getTerminalProposition().equals(components.get(i/2))) {
					comps[i] = 0x7FFFFFFF;
					comps[i + 1] = components.indexOf(components.get(i/2).getSingleInput()) * 2;
					term = i;
				} else if (p.getInitProposition().equals(components.get(i/2))) {
					comps[i] = 0;
					comps[i + 1] = -1;
					init = i;
				} else if (isView) {
					comps[i] = 0x7FFFFFFF;
					comps[i + 1] = -1;
				}
			} else { //Component
				comps[i] = getComp(components.get(i/2));
				comps[i + 1] = -1;
			}

			//fill the structure array:
			structure[i/2] = new int[components.get(i/2).getOutputs().size()];
			for (int j = 0; j < structure[i/2].length; j ++) {
				structure[i/2][j] = components.indexOf(components.get(i/2).getOutputarr()[j]) * 2;
			}
		}

		Set<Component> visited = new HashSet<Component>();

		for (int i = 0; i < basearr.length; i ++) {
			for (int j = 0; j < structure[basearr[i] / 2].length; j ++) {
				startPropagate(structure[basearr[i] / 2][j], 0, components, visited);
			}
		}
		for (int i = 0; i < inputarr.length; i ++) {
			for (int j = 0; j < structure[inputarr[i] / 2].length; j ++) {
				startPropagate(structure[inputarr[i] / 2][j], 0, components, visited);
			}
		}
		for (Component c : components) {
			if (c instanceof Constant) {
				startPropagate(components.indexOf(c), 0, components, visited);
			}
		}

		initcomps = comps.clone();
	}

	private void optimizePropNet(List<Component> comps, PropNet p) {
		List<Component> toremove = new ArrayList<Component>();
		for (Component c : comps) {
//			if (c instanceof Proposition && !p.getBasePropositions().values().contains(c) &&
//					!p.getInputPropositions().values().contains(c)) {
//				boolean thing = true;
//				for (Role r : p.getRoles()) {
//					if (p.getLegalPropositions().get(r).contains(c)) {
//						thing = false;
//					} else if (p.getGoalPropositions().get(r).contains(c)) {
//						thing = false;
//					}
//				}
//				if (thing && !c.equals(p.getTerminalProposition()) && !c.equals(p.getInitProposition())) {
//					for (Component before : c.getInputs()) {
//						before.getOutputs().addAll(c.getOutputs());
//						before.removeOutput(c);
//					}
//					toremove.add(c);
//					p.getPropositions().remove(c);
//				}
			if (c instanceof Not) {
				if (c.getInputs().size() == 1 && c.getSingleInput().getOutputs().size() == 1) {
					if (c.getSingleInput() instanceof And) {
						((And)c.getSingleInput()).nand = true;
						toremove.add(c);
					} else if (c.getSingleInput() instanceof Or) {
						((Or)c.getSingleInput()).nor = true;
						toremove.add(c);
					}
				}
			}
		}
		comps.removeAll(toremove);
	}
	
	private List<Component> getOrdering(Set<Component> comps) {
		List<Component> order = new ArrayList<Component>();
		Set<Component> temp = new HashSet<Component>();
		while (comps.size() > 0) {
			visit(comps.iterator().next(), order, comps, temp);
		}
		return order;
	}
	
	private void visit(Component c, List<Component> order, Set<Component> notmarked, Set<Component> temp) {
		if (temp.contains(c)) return;
		if (notmarked.contains(c)) {
			temp.add(c);
			for (Component next : c.getOutputs()) {
				visit(next, order, notmarked, temp);
			}
			order.add(0, c);
			temp.remove(c);
			notmarked.remove(c);
		}
	}

	private int[][] copyArr(int[][] original) {
		int[][] result = new int[original.length][2];
		for (int i = 0; i < original.length; i ++) {
			result[i][0] = original[i][0];
			result[i][1] = original[i][1];
		}
		return result;
	}

	private int getComp(Component c) {
		if (c instanceof And) {
			return (((And)c).nand? 0 : 0x80000000) - c.getInputs().size();
		} else if (c instanceof Or) {
			return ((Or)c).nor? 0xFFFFFFFF : 0x7FFFFFFF;
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
		markbases(((PropNetMachineState)state).props);
		for (int i = 0; i < goals.length; i ++) {
			if (((comps[goals[i][0]] >> 31) & 1) == 1 && roles.indexOf(role) == goals[i][1]) {
				return goals[i][2];
			}
		}
		return -1;
	}

	@Override
	public boolean isTerminal(MachineState state) {
		markbases(((PropNetMachineState)state).props);
		return ((comps[comps[term + 1]] >> 31) & 1) == 1;
	}

	@Override
	public List<Role> getRoles() {
		return roles;
	}

	@Override
	public MachineState getInitialState() {
		comps = initcomps.clone();
		for (int i = 0; i < structure[init/2].length; i ++) {
			comps[init] = 0xF0000000;
			propagate(structure[init/2][i], 1);
		}
		boolean[] next = new boolean[basearr.length];
		for (int i = 0; i < basearr.length; i ++) {
			next[i] = (((comps[comps[basearr[i] + 1]] >> 31) & 1) == 1);
		}
		for (int i = 0; i < structure[init/2].length; i ++) {
			comps[init] = 0x0;
			propagate(structure[init/2][i], -1);
		}
		return new PropNetMachineState(next);
	}

	@Override
	public List<Move> getLegalMoves(MachineState state, Role role) throws MoveDefinitionException {
		markbases(((PropNetMachineState)state).props);
		ArrayList<Move> moves = new ArrayList<Move>();
		for (int i = 0; i < legals.length; i ++) {
			if (((comps[comps[legalarr[i][0] + 1]] >> 31) & 1) == 1 && legalarr[i][1] == roles.indexOf(role)) {
				moves.add(legals[i]);
			}
		}
		return moves;
	}

	@Override
	public MachineState getNextState(MachineState state, List<Move> moves) throws TransitionDefinitionException {
		markbases(((PropNetMachineState)state).props);
		boolean[] inputs = new boolean[inputarr.length];
		for (int i = 0; i < moves.size(); i ++) {
			inputs[inputmap.get(new RoleMove(moves.get(i), i))] = true;
		}
		markinputs(inputs);
		boolean[] next = new boolean[basearr.length];
		for (int i = 0; i < basearr.length; i ++) {
			next[i] = (((comps[comps[basearr[i] + 1]] >> 31) & 1) == 1);
		}
		return new PropNetMachineState(next);
	}

	private void markbases(boolean[] bases) {
		for (int i = 0; i < bases.length; i ++) {
			if (bases[i] != (((comps[basearr[i]] >> 31) & 1) == 1)) {
				comps[basearr[i]] = bases[i] ? 0xF0000000 : 0x0F000000;
				for (int j = 0; j < structure[basearr[i] / 2].length; j ++) {
					propagate(structure[basearr[i] / 2][j], bases[i] ? 1 : -1);
				}
			}
		}
	}

	private void markinputs(boolean[] inputs) {
		for (int i = 0; i < inputs.length; i ++) {
			if (inputs[i] != (((comps[inputarr[i]] >> 31) & 1) == 1)) {
				comps[inputarr[i]] = inputs[i] ? 0xF0000000 : 0x0F000000;
				for (int j = 0; j < structure[inputarr[i] / 2].length; j ++) {
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
				for (int i = 0; i < structure[index / 2].length; i ++) {
					propagate(structure[index / 2][i], old);
				}
			}
		}
	}

	//real index of the thing * 2 is index.
	private void startPropagate(int index, int newValue, List<Component> components, Set<Component> visited) {
		if (comps[index + 1] != -1) {
			return;
		}
		int old = ((comps[index] >> 31) & 1);
		comps[index] += newValue;
		if (old != ((comps[index] >> 31) & 1) || (newValue == 0 && (old == 0 ||
				!visited.contains(components.get(index/2))))) {
			visited.add(components.get(index/2));
			for (int i = 0; i < structure[index / 2].length; i ++) {
				startPropagate(structure[index / 2][i], ((comps[index] >> 31) & 1), components, visited);
			}
		}
	}
}
