import java.io.Serializable;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
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
	static boolean defined;
	boolean use_propnet_reset = false;

	boolean kill = false;

	PropNet p;
	ArrayList<Proposition> props;
	List<Component> components;

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

	private void findComponentsBackwards(Component current, Set<Component> visited) {
		Queue<Component> queue = new LinkedList<>();
		queue.add(current);
		while (!queue.isEmpty()) {
			current = queue.poll();
			if (visited.contains(current)) continue;
			visited.add(current);
			for (Component parent : current.getInputs()) {
				queue.offer(parent);
			}
		}
	}

	private boolean isCyclic(PropNet p) {
		Set<Component> visited = new HashSet<>();
		Set<Component> stackSet = new HashSet<>();
		for (Component c : p.getComponents()) {
			if (isCyclic(p, visited, stackSet, c)) return true;
		}
		return false;
	}

	private boolean isCyclic(PropNet p, Set<Component> visited, Set<Component> stack, Component v) {
		if (!visited.contains(v)) {
			visited.add(v);
			stack.add(v);
			for (Component c : v.getOutputs()) {
				if (c instanceof Transition) continue;
				if (!visited.contains(c) && isCyclic(p, visited, stack, c)) return true;
				if (stack.contains(c)) return true;
			}
		}
		stack.remove(v);
		return false;
	}

	protected void setPropNet(List<Gdl> description) throws InterruptedException {
		long start = System.currentTimeMillis();
		long time = 0;
		p = OptimizingPropNetFactory.create(description, false);
		time = System.currentTimeMillis() - start;
		Log.println("propnet factory finished in " + time + " ms.");
		Log.println("number of comps: " + p.getSize());
		// trim unnecessary propositions
		int oldSize = 0;
		for (int round = 1; oldSize != p.getSize(); round++) {
			oldSize = p.getSize();

			Log.println("optimizing propnet: round " + round);
			Set<Component> critical = new HashSet<>();
			critical.add(p.getTerminalProposition());
			critical.addAll(p.getInputPropositions().values());
			for (Role role : p.getRoles()) {
				critical.addAll(p.getGoalPropositions().get(role));
				critical.addAll(p.getLegalPropositions().get(role));
			}
			Set<Component> important = new HashSet<>();
			for (Component comp : critical) {
				findComponentsBackwards(comp, important);
			}
			Set<Component> unimportant = new HashSet<>(p.getComponents());
			unimportant.removeAll(important);
			for (Component comp : unimportant) {
				p.removeComponent(comp);
			}
			Log.println("\ttrimmed " + unimportant.size() + " irrelevant comps");

			// removing single-input components
			// i.e. are anything that has one input (i.e. anon, view props)
			// exceptions: NOT, TRANSITION, CONSTANT, and non-view propositions.

			critical.addAll(p.getBasePropositions().values());
			critical.add(p.getInitProposition());

			int ntrimmed = 0;
			Set<Component> compsCopy = new HashSet<>(p.getComponents());
			for (Component c : compsCopy) {
				if (c instanceof Not) continue;
				if (c instanceof Transition) continue;
				if (c instanceof Constant) continue;
				if (critical.contains(c)) continue;
				if (c.getInputs().size() != 1) continue;
				Component in = c.getSingleInput();
				for (Component out : c.getOutputs()) {
					in.addOutput(out);
					out.addInput(in);
				}
				p.removeComponent(c);
				ntrimmed++;
			}
			Log.println("\ttrimmed " + ntrimmed + " single-input comps");

			// if two components have the same inputs and are the same type,
			// then we can condense them
			compsCopy = new HashSet<>(p.getComponents());
			ntrimmed = 0;
			Map<Set<Component>, List<Component>> inputMaps = new HashMap<>();
			for (Component c : compsCopy) {
				if (c instanceof Transition) continue;
				if (c instanceof Constant) continue;
				if (critical.contains(c)) continue;
				if (!inputMaps.containsKey(c.getInputs())) {
					inputMaps.put(c.getInputs(), new ArrayList<>());
				}
				List<Component> possibles = inputMaps.get(c.getInputs());
				if (condenseDuplicates(c, possibles)) ntrimmed++;
			}

			Log.println("\tmerged " + ntrimmed + " duplicate comps");

			Log.println("\tcomps remaining: " + p.getSize());
		}

		// cycle detection
		use_propnet_reset = isCyclic(p);
		if (use_propnet_reset) {
			Log.println("propnet has cycles. differential propagation OFF");
		} else {
			Log.println("propnet is acyclic. differential propagation ON");
		}

		time = System.currentTimeMillis() - start;
		Log.println("propnet created in " + time + " ms");
	}

	public boolean condenseDuplicates(Component c, List<Component> possibles) {
		for (Component poss : possibles) {
			if (!c.getClass().equals(poss.getClass())) continue;
			for (Component next : c.getOutputs()) {
				poss.addOutput(next);
				next.addInput(poss);
			}
			p.removeComponent(c);
			return true;
		}
		// failed
		possibles.add(c);
		return false;
	}

	@Override
	public void initialize(List<Gdl> description) {
		p = null;
		try {
			setPropNet(description);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}

		if (kill) return;
		components = getOrdering(new ArrayList<Component>(p.getComponents()),
				new HashSet<Proposition>(p.getBasePropositions().values()),
				new HashSet<Proposition>(p.getInputPropositions().values()));
		List<Component> legaltoinputhelper = new ArrayList<Component>();
		for (Component c : components) {
			c.crystalize();
		}
		if (kill) return;

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

		Set<Proposition> basepropset = new HashSet<Proposition>(p.getBasePropositions().values());
		Set<Proposition> inputpropset = new HashSet<Proposition>(p.getInputPropositions().values());

		int base = 0;
		int input = 0;
		int legal = 0;
		int goal = 0;
		Map<Component, Integer> indexMap = new HashMap<>();
		for (int i = 0; i < components.size(); i++) {
			indexMap.put(components.get(i), i);
		}
		// Fill the components array
		for (int i = 0; i < components.size() * 2; i += 2) {
			if (kill) return;
			Component component = components.get(i / 2);
			if (!(component instanceof Proposition)) {
				comps[i] = getComp(components.get(i / 2));
				comps[i + 1] = -1;
			} else if (basepropset.contains(component)) {
				comps[i] = 0;
				comps[i + 1] = indexMap.get(component.getSingleInput()) * 2;
				basearr[base] = i;
				props.add((Proposition) component);
				base++;
			} else if (inputpropset.contains(component)) {
				comps[i] = 0;
				comps[i + 1] = 0;
				inputarr[input] = i;
				for (Role r : roles) {
					if (p.getLegalPropositions().get(r)
							.contains(p.getLegalInputMap().get(component))) {
						inputmap.put(
								new RoleMove(new Move(((Proposition) component).getName().get(1)),
										roles.indexOf(r)),
								input);
					}
				}
				input++;
			} else {
				boolean isView = true;
				for (Role r : roles) {
					if (p.getGoalPropositions().get(r).contains(component)) {
						comps[i] = 0x7FFFFFFF;
						comps[i + 1] = -1;
						goals[goal][0] = indexMap.get(component.getSingleInput()) * 2;
						goals[goal][1] = roles.indexOf(r);
						goals[goal][2] = getGoalValue((Proposition) component);
						goal++;
						isView = false;
						break;
					}
					if (p.getLegalPropositions().get(r).contains(component)) {
						comps[i] = 0x7FFFFFFF;
						comps[i + 1] = -1;
						legaltoinputhelper.add(p.getLegalInputMap().get(component));
						legalarr[legal][0] = indexMap.get(component.getSingleInput()) * 2;
						legalarr[legal][1] = roles.indexOf(r);
						legals[legal] = new Move(((Proposition) component).getName().get(1));
						legal++;
						isView = false;
						break;
					}
				}
				if (p.getTerminalProposition().equals(component)) {
					comps[i] = 0x7FFFFFFF;
					comps[i + 1] = indexMap.get(component.getSingleInput()) * 2;
					term = i;
				} else if (p.getInitProposition().equals(component)) {
					comps[i] = 0;
					comps[i + 1] = -1;
					init = i;
				} else if (isView) {
					comps[i] = 0x7FFFFFFF;
					comps[i + 1] = -1;
				}
			}

			// fill the structure array:
			structure[i / 2] = new int[component.getOutputs().size()];
			for (int j = 0; j < structure[i / 2].length; j++) {
				Component out = component.getOutputarr()[j];
				structure[i / 2][j] = indexMap.get(out) * 2;
			}
		}

		legaltoinput = new int[legal];
		for (int i = 0; i < legaltoinputhelper.size(); i++) {
			for (int j = 0; j < inputarr.length; j++) {
				if (components.get(inputarr[j] / 2) == legaltoinputhelper.get(i)) {
					legaltoinput[i] = j;
					break;
				}
			}
		}

		for (Component c : components) {
			if (c instanceof Proposition) continue;
			int delta = getComp(c) - comps[indexMap.get(c) * 2];
			for (Component d : c.getInputs()) {
				delta += ((comps[indexMap.get(d) * 2] >> 31) & 1);
			}
			propagate(indexMap.get(c) * 2, delta);
		}

		initcomps = comps.clone();
		initInternalDC();
	}

	private List<Component> getOrdering(List<Component> comps, Set<Proposition> bases,
			Set<Proposition> inputs) {
		List<Component> order = new ArrayList<Component>();
		int index = 0;
		for (Component c : comps) {
			if (bases.contains(c)) {
				order.add(0, c);
				index++;
			} else if (inputs.contains(c)) {
				order.add(index, c);
			} else {
				order.add(c);
			}
		}
		return order;
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
		resetPropnet();
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

	protected void propagate(int index, int newValue) {
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

	/* ########################################################################################## */

	int[] moves;
	int[] counts;
	int[] indicies;
	boolean[] inputs;

	public void initInternalDC() {
		moves = new int[roles.size()];
		counts = new int[roles.size()];
		indicies = new int[roles.size()];
		inputs = new boolean[inputarr.length];
	}

	public int[] internalDC(PropNetMachineState MS) {
		boolean[] state = MS.props.clone();
		last = null;
		while (!internalTerminal(state)) {
			internalRandomNextState(moves, counts, indicies, state, inputs);
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

	private void internalRandomNextState(int[] moves, int[] counts, int[] indicies, boolean[] state,
			boolean[] inputs) {
		for (int i = 0; i < moves.length; i++) {
			inputs[moves[i]] = false;
		}
		internalRandomJoint(moves, counts, indicies);
		internalNextState(moves, state, inputs);
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

	public boolean[] internalNextState(int[] moves, boolean[] state, boolean[] inputs) {
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

	protected void internalMarkbases(boolean[] bases) {
		resetPropnet();
		for (int i = 0; i < bases.length; i++) {
			if (bases[i] != (((comps[basearr[i]] >> 31) & 1) == 1)) {
				comps[basearr[i]] = bases[i] ? 0xF0000000 : 0x0F000000;
				for (int j = 0; j < structure[basearr[i] / 2].length; j++) {
					propagate(structure[basearr[i] / 2][j], bases[i] ? 1 : -1);
				}
			}
		}
	}

	protected void resetPropnet() {
		if (use_propnet_reset) {
			for (int i = 0; i < comps.length; i++) {
				comps[i] = initcomps[i];
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
