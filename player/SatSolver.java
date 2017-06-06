import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.concurrent.BlockingQueue;
import java.util.stream.Collectors;

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

abstract class Solver extends Thread {
	public boolean kill = false;
	public int best_reward;
	public Stack<Move> best;
}

public class SatSolver extends Solver {
	private JustKiddingPropNetStateMachine machine;
	private Role role;
	private long timeout;
	private BlockingQueue<Solver> out;

	public SatSolver(BlockingQueue<Solver> out, StateMachine machine, Role role, long timeout) {
		this.out = out;
		this.machine = (JustKiddingPropNetStateMachine) machine;
		this.role = role;
		this.timeout = timeout;
	}

	@Override
	public String toString() {
		return "sat solver";
	}

	@Override
	public void run() {
		try {
			solve_();
		} catch (Exception e) {
			e.printStackTrace();
		}
		out.add(this);
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
			if (System.currentTimeMillis() > timeout || kill) {
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
				Set<Component> inputComps = comp.getInputs();
				VecInt vec = new VecInt(inputComps.size());
				VecInt nvec = new VecInt(inputComps.size());
				for (Component in : inputComps) {
					vec.push(compMap.get(in));
					nvec.push(nextCompMap.get(in));
				}
				if (comp instanceof And) {
					solver.and(key, vec);
					solver.and(nkey, nvec);
				} else {
//					printComponent(comp, "");
					solver.or(key, vec);
					solver.or(nkey, nvec);
				}
			} else if (comp instanceof Proposition) {
				// if (bases.contains(comp)) {
				// System.out.println(getName(comp));
				// printComponent(comp.getSingleInput().getSingleInput(), " ");
				// }
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
			if (System.currentTimeMillis() > timeout || kill) {
				Log.println("sat: timeout");
				return;
			}
			for (Component legal : ourLegals) {
				if (impliesIllegal(legal, does)) {
					int key1 = compMap.get(does);
					int key2 = compMap.get(legalInputMap.get(legal));
					if (key1 == key2) continue;
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
		List<Move> output = new ArrayList<>();
		if (checkSolution(winMoves, output)) {
			Log.println("sat: solution verified. time: " + (System.currentTimeMillis() - start));
			best_reward = MyPlayer.MAX_SCORE;
			best = new Stack<>();
			for (int i = output.size() - 1; i >= 0; i--) {
				best.push(output.get(i));
			}
		} else {
			Log.println("sat: solution was incorrect");
		}
	}

	private String getName(Component comp) {
		String toParse = comp.toString();
		int start = toParse.indexOf("label=\"") + 7;
		int end = toParse.indexOf("\"", start);
		return toParse.substring(start, end);
	}

	private void printComponent(Component component, String indent) {
		if (component instanceof Transition) return;
		System.out.println(
				indent + getName(component) + component.getOutputs().stream().map(this::getName)
						.collect(Collectors.toList()));
		indent += " ";
		for (Component inp : component.getInputs()) {
			printComponent(inp, indent);
		}
	}

	private boolean checkSolution(Set<Proposition> moves, List<Move> output)
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
}
