import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.ggp.base.util.gdl.grammar.GdlSentence;
import org.ggp.base.util.propnet.architecture.Component;
import org.ggp.base.util.propnet.architecture.PropNet;
import org.ggp.base.util.propnet.architecture.components.And;
import org.ggp.base.util.propnet.architecture.components.Constant;
import org.ggp.base.util.propnet.architecture.components.Not;
import org.ggp.base.util.propnet.architecture.components.Or;
import org.ggp.base.util.propnet.architecture.components.Proposition;
import org.ggp.base.util.propnet.architecture.components.Transition;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.prover.query.ProverQueryBuilder;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.GateTranslator;

public class SatSolver extends Thread {
	private JustKiddingPropNetStateMachine machine;
	private Role role;
	private long timeout;

	public List<Move> output = null;

	public SatSolver(StateMachine machine, Role role, long timeout) {
		this.machine = (JustKiddingPropNetStateMachine) machine;
		this.role = role;
		this.timeout = timeout;
	}

	@Override
	public void run() {
		try {
			solve_();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	public void solve_() throws ContradictionException, TimeoutException, MoveDefinitionException,
			TransitionDefinitionException, GoalDefinitionException {
		long start = System.currentTimeMillis();
		PropNet p = machine.p;

		// get goal proposition
		Proposition goal100 = null;
		for (Proposition goal : p.getGoalPropositions().get(role)) {
			if (goal.getName().get(1).toString().equals("100")) goal100 = goal;
		}
		if (goal100 == null) {
			Log.println("sat: could not find 100 goal");
			return;
		}

		Map<Component, Integer> compMap = new HashMap<>();
		Map<Component, Integer> nextCompMap = new HashMap<>();
		List<Component> compList = new ArrayList<>();
		compList.add(null); // 1-index
		int nComp = 0;
		for (Component comp : p.getComponents()) {
			compMap.put(comp, ++nComp);
			nextCompMap.put(comp, ++nComp);
			compList.add(comp);
			compList.add(comp);
		}
		compList.add(null);

		GateTranslator solver = new GateTranslator(SolverFactory.instance().defaultSolver());
		VecInt goalVec = new VecInt(2);
		int GOAL_LITERAL = nComp + 1;
		goalVec.push(GOAL_LITERAL);
		solver.addClause(goalVec);

		solver.and(GOAL_LITERAL, nextCompMap.get(p.getTerminalProposition()),
				nextCompMap.get(goal100));
		VecInt known = new VecInt();

		Set<Proposition> bases = new HashSet<>(p.getBasePropositions().values());

		Set<GdlSentence> legalDoeses = new HashSet<>();
		PropNetMachineState initial = (PropNetMachineState) machine.getInitialState();
		for (Move move : machine.getLegalMoves(initial, role)) {
			legalDoeses.add(ProverQueryBuilder.toDoes(role, move));
		}

		VecInt ourInputVec = new VecInt();
		Set<Proposition> ourInputs = new HashSet<>();
		Set<Proposition> ourLegals = p.getLegalPropositions().get(role);
		Map<Proposition, Proposition> legalInputMap = p.getLegalInputMap();
		for (Proposition legal : ourLegals) {
			Proposition does = legalInputMap.get(legal);
			if (legalDoeses.contains(does.getName())) {
				ourInputs.add(does);
				ourInputVec.push(compMap.get(does));
			}
		}
		solver.addAtLeast(ourInputVec, 1);

		boolean[] initialProps = initial.props;
		Set<Proposition> inits = new HashSet<>();
		for (int i = 0; i < machine.props.size(); i++) {
			if (initialProps[i]) inits.add(machine.props.get(i));
		}

		for (Component comp : p.getComponents()) {
			if (System.currentTimeMillis() > timeout) {
				Log.println("sat: timeout");
				return;
			}
			int key = compMap.get(comp);
			int nkey = nextCompMap.get(comp);
			if (comp instanceof Constant) {
				known.push(((Constant) comp).getValue() ? key : -key);
				known.push(((Constant) comp).getValue() ? nkey : -nkey);
			} else if (comp instanceof Transition) {
				known.push(-key);
				solver.not(-nkey, compMap.get(comp.getSingleInput()));
			} else if (comp instanceof Not) {
				solver.not(key, compMap.get(comp.getSingleInput()));
				solver.not(nkey, nextCompMap.get(comp.getSingleInput()));
			} else if (comp instanceof And || comp instanceof Or) {
				Set<Component> ands = new HashSet<>();
				Set<Component> ors = new HashSet<>();
				if (isOredDoesesInDisguise(comp, ands, ors)) {
					VecInt andvec = new VecInt();
					for (Component and : ands) {
						andvec.push(compMap.get(and));
					}
					Set<Component> otherMoves = new HashSet<>(ourInputs);
					otherMoves.removeAll(ors);
					// TODO
					// Log.println(ands);
					// Log.println(ors);
					// Log.println(otherMoves);
					// printInputs(comp, "");
					for (Component move : otherMoves) {
						andvec.push(-compMap.get(move));
					}
					solver.and(key, andvec);
					continue;
				}
				boolean isAnd = comp instanceof And;
				Set<Component> inputComps = comp.getInputs();
				VecInt vec = new VecInt(inputComps.size());
				VecInt nvec = new VecInt(inputComps.size());
				if (isAllDoes(comp)) {
					Set<Component> otherMoves = new HashSet<>(ourInputs);
					otherMoves.removeAll(inputComps);
					for (Component in : otherMoves) {
						vec.push(-compMap.get(in));
						nvec.push(-nextCompMap.get(in));
					}
					isAnd = true;
				} else {
					for (Component in : inputComps) {
						vec.push(compMap.get(in));
						nvec.push(nextCompMap.get(in));
					}
				}
				if (isAnd) {
					solver.and(key, vec);
					solver.and(nkey, nvec);
				} else {
					solver.or(key, vec);
					solver.or(nkey, nvec);
				}
			} else if (comp instanceof Proposition) {
				if (bases.contains(comp)) {
					known.push(inits.contains(comp) ? key : -key);
					solver.not(-nkey, nextCompMap.get(comp.getSingleInput()));
				} else if (comp.getInputs().size() == 0) { // input prop
					if (!ourInputs.contains(comp)) {
						known.push(-key);
					}
					known.push(-nkey);
				} else { // view or other prop
					solver.not(-key, compMap.get(comp.getSingleInput()));
					solver.not(-nkey, nextCompMap.get(comp.getSingleInput()));
				}
			} else Log.println("unknown component type " + comp.getClass());
		}
		Log.println("sat: propnet translated");
		for (Component does : ourInputs) {
			if (System.currentTimeMillis() > timeout) {
				Log.println("sat: timeout");
				return;
			}
			for (Component legal : ourLegals) {
				if (impliesIllegal(legal, does)) {
					int key1 = compMap.get(does);
					int key2 = compMap.get(legalInputMap.get(legal));
					if (key1 == key2) continue;
					// TODO Log.println(parseLabel(does) + " => not " + parseLabel(legal));
					VecInt vec = new VecInt(2);
					vec.push(key1);
					vec.push(key2);
					solver.addAtMost(vec, 1);
				}
			}
		}

		Log.println("sat: move restrictions translated. running solver...");
		solver.setTimeoutMs(timeout - System.currentTimeMillis());
		int[] model = null;
		try {
			model = solver.findModel(known);
		} catch (TimeoutException e) {
			Log.println("sat: timeout in solver");
			return;
		}
		if (model == null) {
			Log.println("sat: failed to find solution");
			return;
		}
		Log.println("sat: found possible solution");
		Set<Proposition> winMoves = toProps(model, compList, ourInputs);
		output = new ArrayList<>();
		if (checkSolution(winMoves)) {
			Log.println("sat: solution verified. time: " + (System.currentTimeMillis() - start));
		} else {
			output = null;
			Log.println("sat: solution was incorrect");
		}
	}

	private boolean checkSolution(Set<Proposition> moves)
			throws GoalDefinitionException, MoveDefinitionException, TransitionDefinitionException {
		MachineState state = machine.getInitialState();
		for (Proposition pmove : moves) {
			Move move = Move.create(pmove.getName().get(1).toString());
			if (!machine.findLegals(role, state).contains(move)) return false;
			state = machine.getRandomNextState(state, role, move);
			output.add(move);
		}
		return machine.isTerminal(state) && machine.findReward(role, state) == MyPlayer.MAX_SCORE;
	}

	private boolean isOredDoesesInDisguise(Component root, Set<Component> andOut,
			Set<Component> orOut) {
		if (!(root instanceof Or)) return false;
		boolean foundAndClause = false;
		for (Component child : root.getInputs()) {
			child = sanitize(child);
			if (!(child instanceof And)) return false;
			Set<Component> inputs = new HashSet<>();
			for (Component child2 : child.getInputs()) {
				child2 = sanitize(child2);
				if (isAllDoes(child2)) {
					for (Component does : child2.getInputs()) {
						orOut.add(does);
					}
				} else inputs.add(child2);
			}
			if (foundAndClause && !inputs.equals(andOut)) return false;
			andOut.addAll(inputs);
		}
		return true;
	}

	private Component sanitize(Component root) {
		while (!(root instanceof Not) && root.getInputs().size() == 1) {
			Component next = root.getSingleInput();
			if (next instanceof Transition) return root;
			root = root.getSingleInput();
		}
		return root;
	}

	private Set<Proposition> toProps(int[] model, List<Component> compList,
			Set<Proposition> ourInputs) {
		Set<Proposition> inputs = new HashSet<>();
		for (int i = 0; i < model.length; i++) {
			int elem = model[i];
			if (elem < 0) continue;
			if (elem >= compList.size()) continue;
			Component comp = compList.get(elem);
			if (ourInputs.contains(comp)) {
				Proposition prop = (Proposition) compList.get(elem);
				inputs.add(prop);
			}
		}
		return inputs;
	}

	private boolean backpropagate(Component start, Component does, boolean reachedNot,
			boolean reachedTransition) {
		if (start instanceof Not) reachedNot = true;
		if (reachedNot && start instanceof And) return false;
		if (!reachedNot && start instanceof Or) return false;
		if (start instanceof Transition) {
			if (reachedTransition) return false;
			reachedTransition = true;
		}
		if (start == does) return reachedNot && reachedTransition;
		for (Component in : start.getInputs()) {
			if (backpropagate(in, does, reachedNot, reachedTransition)) {
				return true;
			}
		}
		return false;
	}

	private boolean impliesIllegal(Component legal, Component does) {
		return backpropagate(legal, does, false, false);
	}

	private boolean isAllDoes(Component comp) {
		if (!(comp instanceof Or)) return false;
		for (Component in : comp.getInputs()) {
			if (!(in instanceof Proposition)) return false;
			if (!(((Proposition) in).getName().getName().toString().equals("does"))) return false;
		}
		return true;
	}

	private String parseLabel(Component c) {
		String comp = c.toString();
		int start = comp.indexOf("label=\"") + 7;
		int end = comp.indexOf("\"", start);
		return comp.substring(start, end);
	}

	private void printInputs(Component comp, String indent) {
		if (comp instanceof Transition) return;
		Log.println(indent + parseLabel(comp));// + " " + isAllDoes(comp));
		for (Component in : comp.getInputs()) {
			// in = sanitize(in);
			printInputs(in, indent + "  ");
		}
	}

	private static void test() throws ContradictionException, TimeoutException {
		GateTranslator translate = new GateTranslator(SolverFactory.instance().defaultSolver());
		VecInt solution = new VecInt(1);
		solution.push(1);
		translate.addClause(solution);
		translate.xor(1, 2, 3);
		VecInt assume = new VecInt(1);
		translate.not(2, -3);
		int[] model = translate.findModel();
		System.out.println(Arrays.toString(model));
	}

	public static void main(String[] args) {
		try {
			test();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
}
