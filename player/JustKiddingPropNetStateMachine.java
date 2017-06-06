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
import org.ggp.base.util.gdl.grammar.GdlDistinct;
import org.ggp.base.util.gdl.grammar.GdlFunction;
import org.ggp.base.util.gdl.grammar.GdlLiteral;
import org.ggp.base.util.gdl.grammar.GdlPool;
import org.ggp.base.util.gdl.grammar.GdlRelation;
import org.ggp.base.util.gdl.grammar.GdlRule;
import org.ggp.base.util.gdl.grammar.GdlSentence;
import org.ggp.base.util.gdl.grammar.GdlTerm;
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
import org.ggp.base.util.statemachine.cache.CachedStateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.prover.ProverStateMachine;

public class JustKiddingPropNetStateMachine extends StateMachine {

	int[] comps;
	int[] initcomps;
	int[][] structure;
	List<Role> roles;
	Map<Role, List<Move>> actions;
	int term;
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
	PropNetMachineState initial_state;

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

	private void sanitizeDistinctHelper(Gdl gdl, List<Gdl> in, List<Gdl> out) {
		if (!(gdl instanceof GdlRule)) {
			out.add(gdl);
			return;
		}
		GdlRule rule = (GdlRule) gdl;
		for (GdlLiteral lit : rule.getBody()) {
			if (lit instanceof GdlDistinct) {
				GdlDistinct d = (GdlDistinct) lit;
				GdlTerm a = d.getArg1();
				GdlTerm b = d.getArg2();
				if (!(a instanceof GdlFunction) && !(b instanceof GdlFunction)) continue;
				if (!(a instanceof GdlFunction && b instanceof GdlFunction)) return;
				GdlSentence af = ((GdlFunction) a).toSentence();
				GdlSentence bf = ((GdlFunction) b).toSentence();
				if (!af.getName().equals(bf.getName())) return;
				if (af.arity() != bf.arity()) return;
				for (int i = 0; i < af.arity(); i++) {
					List<GdlLiteral> ruleBody = new ArrayList<>();
					for (GdlLiteral newLit : rule.getBody()) {
						if (newLit != lit) ruleBody.add(newLit);
						else ruleBody.add(GdlPool.getDistinct(af.get(i), bf.get(i)));
					}
					GdlRule newRule = GdlPool.getRule(rule.getHead(), ruleBody);
					Log.println("new rule: " + newRule);
					in.add(newRule);
				}
				return;
			}
		}
		for (GdlLiteral lit : rule.getBody()) {
			if (lit instanceof GdlDistinct) {
				Log.println("distinct rule added: " + rule);
				break;
			}
		}
		out.add(rule);
	}

	private List<Gdl> sanitizeDistinct(List<Gdl> description) {
		List<Gdl> out = new ArrayList<>();
		for (int i = 0; i < description.size(); i++) {
			sanitizeDistinctHelper(description.get(i), description, out);
		}
		return out;
	}

	protected void setPropNet(List<Gdl> description) throws InterruptedException {

		long start = System.currentTimeMillis();
		long time = 0;
		description = sanitizeDistinct(description);
		p = OptimizingPropNetFactory.create(description, false);
		time = System.currentTimeMillis() - start;
		Log.println("propnet factory finished in " + time + " ms.");
		Log.println("number of comps: " + p.getSize());
		Log.println("number of links: " + p.getNumLinks());
		Log.println("number of props: " + p.getPropositions().size());
		Log.println("number of bases: " + p.getBasePropositions().size());
		// trim unnecessary propositions

		try {
			PropNetOptimizer.optimizePropnet(p);
		} catch (InstantiationException | IllegalAccessException e) {
			e.printStackTrace();
		}
		p.renderToFile("graph.dot");

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
				} else if (p.getInitProposition() != null
						&& p.getInitProposition().equals(component)) {
					comps[i] = 0;
					comps[i + 1] = -1;
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
		Log.println("finding initial state...");
		StateMachine prover = new CachedStateMachine(new ProverStateMachine());
		prover.initialize(description);
		Set<GdlSentence> initial = new HashSet<>(prover.getInitialState().getContents());
		boolean[] initbases = new boolean[basearr.length];
		assert basearr.length == props.size();
		for (int i = 0; i < basearr.length; i++) {
			initbases[i] = initial.contains(props.get(i).getName());
		}
		initial_state = new PropNetMachineState(initbases);
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
		return initial_state;
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
