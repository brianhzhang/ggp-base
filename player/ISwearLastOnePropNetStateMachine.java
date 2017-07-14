import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.ggp.base.util.gdl.grammar.Gdl;
import org.ggp.base.util.gdl.grammar.GdlConstant;
import org.ggp.base.util.gdl.grammar.GdlRelation;
import org.ggp.base.util.propnet.architecture.Component;
import org.ggp.base.util.propnet.architecture.PropNet;
import org.ggp.base.util.propnet.architecture.components.And;
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

public class ISwearLastOnePropNetStateMachine extends StateMachine {

	List<Role> roles;
	int[] comps;
	int[] initcomps;
	int[] structure;
	Map<Role, List<Move>> actions;
	Map<Move, Integer> inputmap;
	Move[] legalarr; //fast creation of lists of moves.
	int[] bases; //mappings to the corresponding base/input propositions
	int[] inputs;
	int[] legals;
	int[] nots;
	int[] goals;
	int init;
	int terminal;
	PropNet p;
	ArrayList<Proposition> props;

	@Override
	public void initialize(List<Gdl> description) {
		p = null;
		try {
			p = OptimizingPropNetFactory.create(description);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		roles = p.getRoles();
		List<Component> components = new ArrayList<Component>(p.getComponents());
		//		optimizePropNet(components, p);
		comps = new int[components.size() * 3];
		List<Integer> tempStructure = new ArrayList<Integer>();
		actions = new HashMap<Role, List<Move>>();
		legalarr = new Move[p.getInputPropositions().values().size()];

		bases = new int[p.getBasePropositions().values().size()];
		inputs = new int[p.getInputPropositions().values().size()];
		int size = 0;
		for (Role r : roles) {
			size += p.getLegalPropositions().get(r).size();
		}
		legals = new int[size * 2];
		inputmap = new HashMap<Move, Integer>();

		for (Role r : roles) {
			actions.put(r, propToMoves(p.getLegalPropositions().get(r), true));
		}
		int base = 0;
		int input = 0;
		int legal = 0;
		List<Component> nots = new ArrayList<Component>();
		props = new ArrayList<Proposition>();
		for (int i = 0; i < components.size(); i ++) {
			comps[i * 3] = createComponent(components.get(i), p);
			boolean thing = false;
			if (p.getBasePropositions().values().contains(components.get(i))) {
				comps[i * 3 + 1] = components.indexOf(components.get(i).getSingleInput()) * 3;
				bases[base] = i * 3;
				base ++;
				thing = true;
				props.add((Proposition) components.get(i));
				//System.out.println(components.get(i).getInputs().size() + "    " + ((Proposition) components.get(i)).getName() + "    " + components.get(i).getSingleInput());
			} else if (p.getInputPropositions().values().contains(components.get(i))) {
				comps[i * 3 + 1] = 0x13370420;
				inputmap.put(new Move(((Proposition) components.get(i)).getName().get(1)), input);
				inputs[input] = i * 3;
				input ++;
				thing = true;
			}
			for (Role r : roles) {
				if (p.getLegalPropositions().get(r).contains(components.get(i))) {
					comps[i * 3 + 1] = components.indexOf(components.get(i).getSingleInput()) * 3;
					legalarr[legal] = new Move(((Proposition) components.get(i)).getName().get(1));
					legals[legal * 2] = i * 3;
					for (int j = 0; j < roles.size(); j ++) {
						if (roles.get(j).getName().equals(((Proposition) components.get(i)).getName().getBody().get(0))) {
							legals[legal * 2 + 1] = j;
						}
					}
					legal ++;
					thing = true;
				}
			}
			if (!thing) {
				if (components.get(i) instanceof Proposition) {
					comps[i * 3 + 1] = 0xFFFFFFFF;
				} else {
					if (components.get(i) instanceof Not) {
						nots.add(components.get(i));
					}
					comps[i * 3 + 1] = 0xFFFFFFFE;
				}
			}
			comps[i * 3 + 2] = tempStructure.size();
			tempStructure.add(components.get(i).getOutputs().size());
			for (Component c : components.get(i).getOutputs()) {
				tempStructure.add(components.indexOf(c) * 3);
			}
		}
		terminal = components.indexOf(p.getTerminalProposition().getSingleInput()) * 3;
		init = components.indexOf(p.getInitProposition()) * 3;
		
		structure = new int[tempStructure.size()];
		for (int i = 0; i < tempStructure.size(); i ++) {
			structure[i] = tempStructure.get(i);
		}
		this.nots = new int[nots.size()];
		for (int i = 0; i < nots.size(); i ++) {
			this.nots[i] = components.indexOf(nots.get(i)) * 3;
		}

		List<Proposition> goalprops = new ArrayList<Proposition>();
		for (Role r : roles) {
			goalprops.addAll(p.getGoalPropositions().get(r));
		}
		for (int i = 0; i < bases.length; i ++) {
			for (int j = 0; j < structure[comps[bases[i] + 2]]; j ++) {
				startPropagate(structure[comps[bases[i] + 2] + 1 + j], 0);
			}
		}
		for (int i = 0; i < inputs.length; i ++) {
			for (int j = 0; j < structure[comps[inputs[i] + 2]]; j ++) {
				startPropagate(structure[comps[inputs[i] + 2] + 1 + j], 0);
			}
		}
		
		initcomps = new int[comps.length];
		initcomps = comps.clone();

		goals = new int[goalprops.size() * 3];
		for (int i = 0; i < goalprops.size(); i ++) {
			for (int j = 0; j < p.getRoles().size(); j ++) {
				if (p.getRoles().get(j).getName().equals(goalprops.get(i).getName().getBody().get(0))) {
					goals[i * 3] = components.indexOf(goalprops.get(i).getSingleInput());
					goals[i * 3 + 1] = roles.indexOf(p.getRoles().get(j));
					goals[i * 3 + 2] = getGoalValue(goalprops.get(i));
				}
			}
		}

		//		for (Component c : p.getBasePropositions().values()) {
		//			System.out.println(c.getSingleInput());
		//		}

		//		System.out.println(Arrays.toString(comps));
		//		System.out.println(Arrays.toString(structure));
	}

//	private void optimizePropNet(List<Component> comps, PropNet p) {
//		List<Component> toremove = new ArrayList<Component>();
//		for (Component c : comps) {
//			if (c instanceof Proposition && !c.equals(p.getInitProposition()) && !c.equals(p.getTerminalProposition()) &&
//					!p.getGoalPropositions().containsValue(c)) {
//				if (!(p.getBasePropositions().values().contains(c) || p.getLegalPropositions().values().contains(c) ||
//						p.getInputPropositions().values().contains(c) || p.getGoalPropositions().values().contains(c))) {
//					for (Component before : c.getInputs()) {
//						before.getOutputs().addAll(c.getOutputs());
//						before.removeOutput(c);
//					}
//					toremove.add(c);
//				}
//			} else if (c instanceof Not) {
//				if (c.getInputs().size() == 1 && c.getSingleInput().getOutputs().size() == 1) {
//					if (c.getSingleInput() instanceof And) {
//						((And)c.getSingleInput()).nand = true;
//						toremove.add(c);
//					} else if (c.getSingleInput() instanceof Or) {
//						((Or)c.getSingleInput()).nor = true;
//						toremove.add(c);
//					}
//				}
//			}
//		}
//		comps.removeAll(toremove);
//	}

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

	private int getGoalValue(Proposition goalProposition) {
		GdlRelation relation = (GdlRelation) goalProposition.getName();
		GdlConstant constant = (GdlConstant) relation.get(1);
		return Integer.parseInt(constant.toString());
	}

	private int createComponent(Component c, PropNet p) {
		if (c instanceof Proposition) {
			if (p.getBasePropositions().values().contains(c) || p.getInputPropositions().values().contains(c)) {
				return 0x0F000000;
			} else {
				return 0x13370420;
			}
		} else if (c instanceof Or) {
			return 0x7FFFFFFF;
		} else if (c instanceof And) {
			return 0x80000000 - c.getInputs().size();
		} else if (c instanceof Not) {
			return 0xFFFFFFFF;
		} else if (c instanceof Transition) {
			return 0x7FFFFFFF;
		} else { //  instanceof Constant
			return (c.getValue()) ? 0xF0000000 : 0x0F000000;
		}
	}

	@Override
	public List<Move> findActions(Role role) throws MoveDefinitionException {
		return actions.get(role);
	}

	@Override
	public int getGoal(MachineState state, Role role) throws GoalDefinitionException {
		markbases(((PropNetMachineState)state).props);

		for (int i = 0; i < goals.length; i += 3) {
			if (((comps[goals[i]] >> 31) & 1) == 1 && roles.indexOf(role) == goals[i + 1]) {
				return goals[i + 2];
			}
		}

		throw new GoalDefinitionException(state, role);
	}

	@Override
	public boolean isTerminal(MachineState state) {
		markbases(((PropNetMachineState)state).props);
		return ((comps[terminal] >> 31) & 1) == 1;
	}

	@Override
	public List<Role> getRoles() {
		return roles;
	}

	@Override
	public MachineState getInitialState() {
		//		System.out.println(structure[comps[init + 2]]);
		comps = initcomps.clone();
		for (int j = 0; j < structure[comps[init + 2]]; j ++) {
			propagate(structure[comps[init + 2] + 1 + j], 1);
		}
		boolean[] next = new boolean[bases.length];
		for (int i = 0; i < bases.length; i ++) {
			next[i] = ((comps[comps[bases[i] + 1]] >> 31) & 1) == 1;
		}
		for (int j = 0; j < structure[comps[init + 2]]; j ++) {
			propagate(structure[comps[init + 2] + 1 + j], -1);
		}
		return new PropNetMachineState(next);
	}

	@Override
	public List<Move> getLegalMoves(MachineState state, Role role) throws MoveDefinitionException {
		markbases(((PropNetMachineState)state).props);
		List<Move> moves = new ArrayList<Move>();
		//TODO everything is broken. Lovely.
		for (int i = 0; i < legals.length/2; i ++) {
			if (((comps[comps[legals[i * 2] + 1]] >> 31) & 1) == 1 && roles.indexOf(role) == legals[i * 2 + 1]) {
				moves.add(legalarr[i]);
			}
		}
		return moves;
	}

	@Override
	public MachineState getNextState(MachineState state, List<Move> moves) throws TransitionDefinitionException {
		markbases(((PropNetMachineState)state).props);
		boolean[] inputs = new boolean[this.inputs.length];
		for (Move m : moves) {
			inputs[inputmap.get(m)] = true;
		}
		markinputs(inputs);
		boolean[] next = new boolean[bases.length];
		for (int i = 0; i < bases.length; i ++) {
			next[i] = (((comps[comps[bases[i] + 1]] >> 31) & 1) == 1);
		}
		return new PropNetMachineState(next);
	}

	private void markbases(boolean[] bases) {
		for (int i = 0; i < bases.length; i ++) {
			if (bases[i] != (comps[this.bases[i]] < 0)) {
				comps[this.bases[i]] = (bases[i]) ? 0xF0000000 : 0x0F000000;
				for (int j = 0; j < structure[comps[this.bases[i] + 2]]; j ++) {
					propagate(structure[comps[this.bases[i] + 2] + 1 + j], bases[i] ? 1 : -1);
				}
			}
		}
	}

	private void markinputs(boolean[] inputs) {
		for (int i = 0; i < inputs.length; i ++) {
			if (inputs[i] != (comps[this.inputs[i]] < 0)) {
				comps[this.inputs[i]] = (inputs[i]) ? 0xF0000000 : 0x0F000000;
				for (int j = 0; j < structure[comps[this.inputs[i] + 2]]; j ++) {
					propagate(structure[comps[this.inputs[i] + 2] + 1 + j], inputs[i] ? 1 : -1);
				}
			}
		}
	}

	private void propagate(int index, int newValue){
		if (comps[index + 1] != 0xFFFFFFFE && comps[index + 1] != 0xFFFFFFFF) {
			return;
		}
		if (comps[index + 1] == 0xFFFFFFFF) {
			comps[index] = -newValue;
			for (int i = 0; i < structure[comps[index + 2]]; i ++){
				propagate(structure[comps[index + 2] + i + 1], newValue);
			}
		} else {
			int old = ((comps[index] >> 31) & 1);
			comps[index] += newValue;
			if (old != ((comps[index] >> 31) & 1)) {
				old = ((comps[index] >> 31) & 1) - old;
				for (int i = 0; i < structure[comps[index + 2]]; i ++){
					propagate(structure[comps[index + 2] + i + 1], old);
				}
			}
		}
	}

	private void startPropagate(int index, int newValue) {
		if (comps[index + 1] != 0xFFFFFFFE && comps[index + 1] != 0xFFFFFFFF) {
			return;
		}
		if (comps[index + 1] == 0xFFFFFFFF) {
			comps[index] = -newValue;
			for (int i = 0; i < structure[comps[index + 2]]; i ++){
				startPropagate(structure[comps[index + 2] + i + 1], newValue);
			}
		} else { //component
			int old = ((comps[index] >> 31) & 1);
			comps[index] += newValue;
			boolean not = false;
			for (int i = 0; i < nots.length; i ++) {
				if (index == nots[i]) {
					not = true;
					break;
				}
			}
			if (old != ((comps[index] >> 31) & 1) || not) {
				for (int i = 0; i < structure[comps[index + 2]]; i ++){
					startPropagate(structure[comps[index + 2] + i + 1], ((comps[index] >> 31) & 1));
				}
			}
		}
	}
}
