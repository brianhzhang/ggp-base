import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Queue;
import java.util.Set;
import java.util.Stack;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.TimeUnit;

import org.apache.commons.math3.stat.regression.MillerUpdatingRegression;
import org.apache.commons.math3.stat.regression.RegressionResults;
import org.apache.commons.math3.stat.regression.SimpleRegression;
import org.apache.commons.math3.stat.regression.UpdatingMultipleLinearRegression;
import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.Pair;
import org.ggp.base.util.gdl.grammar.Gdl;
import org.ggp.base.util.gdl.grammar.GdlConstant;
import org.ggp.base.util.gdl.grammar.GdlSentence;
import org.ggp.base.util.gdl.grammar.GdlTerm;
import org.ggp.base.util.propnet.architecture.Component;
import org.ggp.base.util.propnet.architecture.PropNet;
import org.ggp.base.util.propnet.architecture.components.Or;
import org.ggp.base.util.propnet.architecture.components.Proposition;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.prover.query.ProverQueryBuilder;

public class Experiment extends Method {

	public static final int FAIL = MyPlayer.MIN_SCORE - 1;
	private static final boolean USE_MULTIPLAYER_FACTORING = true;
	private static final double EXPLORATION_BIAS_FACTOR = 1.0;
	private double exploration_bias = 1.0;

	private StateMachine[] machines;
	private boolean propNetInitialized = false;
	private MyPlayer player;
	private StateMachine mainThreadMachine;

	private StateMachineCreatorThread smthread;

	// communication between metagame threads
	private Stack<Move> solution;
	private Map<Role, Set<Move>> useless;
	private List<Role> opponents;
	private Map<Proposition, Proposition> legalToInputMap;
	private Map<Proposition, Proposition> inputToLegalMap;
	private int nUsefulRoles;
	private boolean[] ignoreProps;

	// for weighted depth charge results
	private static final double OUR_WEIGHT = 0.9;
	private double oppWeight;
	private Role[] roles;
	private int ourRoleIndex = -1;

	// heuristics
	// GdlTerm --> index into heuristicCalcs
	private UpdatingMultipleLinearRegression heuristicRegression;
	private SimpleRegression dcRegression;
	private List<String> heuristicNames;
	private double heuristic_yint;
	private double heuristic_goalweight;
	private double[] heuristics;
	// for each heuristic in heuristicCalcs, contains the props that affect
	private List<List<Integer>> heuristicProps;
	private double heuristicWeight;
	private MTreeNode root;
	private Map<MachineState, MTreeNode> dagMap;
	private int depthChargesPerState = 1;

	public Experiment(MyPlayer gamer, List<Gdl> description) {
		this.player = gamer;
		machines = new StateMachine[MyPlayer.N_THREADS];
		for (int i = 0; i < MyPlayer.N_THREADS; i++) {
			machines[i] = gamer.getStateMachine();
			machines[i].initialize(description);
		}
		smthread = new StateMachineCreatorThread(gamer.getRole(), description);
		smthread.start();
	}

	private boolean checkStateMachineStatus() {
		if (!propNetInitialized && !smthread.isAlive()) {
			player.switchToNewPropnets(smthread.m, machines);
			Log.println("propnets initialized");
			return propNetInitialized = true;
		}
		return false;
	}

	@SuppressWarnings("serial")
	private static final Move USELESS_MOVE = new Move(new GdlTerm() {

		@Override
		public boolean isGround() {
			return false;
		}

		@Override
		public GdlSentence toSentence() {
			return null;
		}

		@Override
		public String toString() {
			return "[ noop ]";
		}

	});

	private Set<GdlConstant> findClocks(JustKiddingPropNetStateMachine machine) {
		// find clock
		// a clock is
		Set<GdlConstant> possibleClocks = new HashSet<>();
		Set<GdlConstant> notClocks = new HashSet<>();
		int iter = 0;
		boolean changing = true;
		Map<GdlSentence, Integer> forward = new HashMap<>();
		Map<Pair<GdlConstant, Integer>, GdlSentence> backward = new HashMap<>();
		double totLegalMoves = 0;
		double nPly = 0;
		while (iter < 40 * totLegalMoves / nPly || changing) {
			MachineState state = machine.getInitialState();
			int step = 0;
			Map<GdlSentence, Integer> oldForward = new HashMap<>(forward);
			Map<Pair<GdlConstant, Integer>, GdlSentence> oldBackward = new HashMap<>(backward);
			while (!machine.isTerminal(state)) {
				step++;
				Set<GdlSentence> contents = ((PropNetMachineState) state)
						.pnContents(smthread.m.props);
				for (GdlSentence sent : contents) {
					sent = sent.get(0).toSentence();
					GdlConstant name = sent.getName();
					if (notClocks.contains(name)) continue;
					possibleClocks.add(name);
					if (forward.containsKey(sent)) {
						if (forward.get(sent) != step) {
							Log.printf("%s is not the clock: %s found at steps %d and %d\n",
									name, sent, forward.get(sent), step);
							notClocks.add(name);
						}
					} else forward.put(sent, step);

					if (backward.containsKey(Pair.of(name, step))) {
						if (!backward.get(Pair.of(name, step)).equals(sent)) {
							Log.printf("%s is not the clock: at step %d, found both %s and %s\n",
									name, step, backward.get(Pair.of(name, step)), sent);
							notClocks.add(name);
						}
					} else backward.put(Pair.of(name, step), sent);
				}
				for (Proposition base : smthread.m.props) {
					GdlConstant name = base.getName().get(0).toSentence().getName();
					if (notClocks.contains(name)) continue;
					if (!backward.containsKey(Pair.of(name, step))) {
						Log.printf("%s is not the clock: not found at step %d\n",
								name, step);
						notClocks.add(name);
					}
				}
				try {
					nPly += 1;
					totLegalMoves += machine.getLegalMoves(state, roles[ourRoleIndex]).size();
					state = machine.getRandomNextState(state);

				} catch (Exception e) {
					e.printStackTrace();
				}
			}
			changing = !(oldForward.equals(forward) && oldBackward.equals(backward));
			iter++;
		}
		possibleClocks.removeAll(notClocks);
		return possibleClocks;
	}

	@Override
	public void metaGame(StateMachineGamer gamer, long timeout) {
		useless = new HashMap<>();
		solution = null;
		opponents = new ArrayList<>();
		heuristics = null;
		depthChargesPerState = 1;

		StateMachine machine = gamer.getStateMachine();
		roles = machine.findRoles().toArray(new Role[0]);
		for (int i = 0; i < roles.length; i++) {
			Role role = roles[i];
			if (!role.equals(gamer.getRole())) opponents.add(role);
			else ourRoleIndex = i;
			useless.put(role, new HashSet<>());
		}
		Log.println("roles: " + Arrays.toString(roles) + " | our role: " + ourRoleIndex);
		Log.println("method: " + this.getClass().getCanonicalName());
		oppWeight = opponents.size() == 0 ? 0 : (1 - OUR_WEIGHT) / opponents.size();

		try {
			smthread.join(timeout - System.currentTimeMillis());
		} catch (InterruptedException e) {
			e.printStackTrace();
		}

		if (!checkStateMachineStatus()) {
			Log.println("still building propnet...");
			return;
		}

		if (nUsefulRoles != 1) {
			try {
				multiPlayerMetaGame(timeout);
			} catch (Exception e) {
				e.printStackTrace();
			}
			return;
		}

		Log.println("single player game. starting solver");

		machine = gamer.getStateMachine();

		List<Proposition> bases = smthread.m.props;

		boolean[] ignoreProps = new boolean[bases.size()];
		Set<GdlConstant> possibleClocks = findClocks((JustKiddingPropNetStateMachine) machine);
		if (possibleClocks.size() == 0) Log.println("no clock");
		else if (possibleClocks.size() > 1)
			Log.println("too many possible clocks: " + possibleClocks);
		else {
			GdlConstant clockConstant = possibleClocks.iterator().next();
			Log.println("ignoring clock proposition " + clockConstant);
			Map<GdlSentence, Integer> basemap = new HashMap<>();
			for (int i = 0; i < bases.size(); i++) {
				basemap.put(bases.get(i).getName(), i);
			}
			for (GdlSentence g : basemap.keySet()) {
				if (g.get(0).toSentence().getName().equals(clockConstant)) {
					int idx = basemap.get(g);
					ignoreProps[idx] = true;
				}
			}
		}

		PropNet propnet = smthread.m.p;
		class IgnoreList {
			private boolean[] ignore = ignoreProps.clone();
		}

		List<IgnoreList> factors = new ArrayList<>();
		Set<Component> reachable = new HashSet<>(smthread.reachable);

		int nignored = 0;
		for (int i = 0; i < bases.size(); i++) {
			if (!reachable.contains(bases.get(i))) {
				ignoreProps[i] = true;
				nignored++;
			}
		}

		Log.println("ignoring " + nignored + " additional irrelevant props");

		Component terminalGate = propnet.getTerminalProposition();
		while (terminalGate.getInputs().size() == 1) {
			terminalGate = terminalGate.getSingleInput();
		}
		Set<Component> fullReachable = new HashSet<>();
		if (terminalGate instanceof Or) {
			for (Component factor : terminalGate.getInputs()) {
				Set<Component> thisReachable = new HashSet<>();
				findComponentsBackwards(factor, thisReachable);
				IgnoreList ignore = new IgnoreList();
				for (int i = 0; i < bases.size(); i++) {
					if (!thisReachable.contains(bases.get(i))) {
						ignore.ignore[i] = true;
					}
				}
				Set<Component> intersect = new HashSet<>(thisReachable);
				intersect.retainAll(fullReachable);
				if (!intersect.isEmpty()) {
					factors.clear();
					break; // not actually factorable
				}
				fullReachable.addAll(thisReachable);
				fullReachable.retainAll(smthread.m.props);
				factors.add(ignore);
			}
		}

		if (factors.isEmpty()) {
			Log.println("unfactorable game");
			factors.add(new IgnoreList());
		} else {
			Log.println("found " + factors.size() + " factors");
		}

		int n_factor = factors.size();

		BlockingQueue<Solver> returns = new LinkedBlockingQueue<>();

		Solver[] solvers = new Solver[1 + n_factor];
		for (int i = 0; i < n_factor; i++) {
			solvers[i] = new DFSSolver(player.copyMachine((JustKiddingPropNetStateMachine) machine),
					timeout, factors.get(i).ignore, returns, i);
			solvers[i].start();
		}
		solvers[n_factor] = new SatSolver(returns, machine, gamer.getRole(), timeout);
		solvers[n_factor].start();

		long start = System.currentTimeMillis();
		solution = null;

		int best_reward = 0;
		boolean proven = true;

		for (int i = 0; i < solvers.length; i++) {
			try {
				Solver solver = returns.take();
				if (solver.best == null) { // timeout
					Log.println(solver + " found no solution");
					if (solver instanceof DFSSolver) proven = false;
					continue;
				}
				Log.println(solver + " found solution with score " + solver.best_reward);
				if (solver.best_reward > best_reward) {
					best_reward = solver.best_reward;
					solution = solver.best;
					if (best_reward == MyPlayer.MAX_SCORE) break;
				}

			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}

		if (best_reward < MyPlayer.MAX_SCORE && !proven) solution = null;

		for (int i = 0; i < solvers.length; i++) {
			if (solvers[i].isAlive()) {
				solvers[i].kill = true;
				try {
					solvers[i].join();
				} catch (InterruptedException e) {
					e.printStackTrace();
				}
			}
		}

		if (solution != null) {
			Log.println("solver: complete in " + (System.currentTimeMillis() - start) + " ms");
		} else {
			Log.println("solver: failed to find solution");
		}
	}

	private class MetaGameDCThread extends Thread {

		private JustKiddingPropNetStateMachine machine;
		private long timeout;
		private Role role;
		public SimpleRegression[] timeCalc = new SimpleRegression[heuristicNames.size()];

		public MetaGameDCThread(StateMachine machine, Role role, long timeout) {
			this.machine = (JustKiddingPropNetStateMachine) machine;
			this.role = role;
			this.timeout = timeout;
			for (int i = 0; i < timeCalc.length; i++) {
				timeCalc[i] = new SimpleRegression();
			}
		}

		@Override
		public void run() {
			try {
				run_();
			} catch (Exception e) {
				e.printStackTrace();
			}
		}

		public void run_() throws MoveDefinitionException, TransitionDefinitionException {
			MachineState initial = machine.getInitialState();
			int n_heuristic = heuristicNames.size();
			while (System.currentTimeMillis() < timeout) {
				MachineState state = initial;
				int nstep = 0;
				List<double[]> states = new ArrayList<>();
				List<PropNetMachineState> pstates = new ArrayList<>();

				while (!machine.isTerminal(state)) {
					double[] vstate = new double[1 + n_heuristic];
					if (System.currentTimeMillis() > timeout) return;
					PropNetMachineState pstate = (PropNetMachineState) state;
					for (int i = 0; i < n_heuristic; i++) {
						int icount = 0;
						for (int j : heuristicProps.get(i)) {
							if (pstate.props[j]) {
								vstate[i]++;
								icount++;
							}
						}
						timeCalc[i].addData(nstep, icount);
					}
					vstate[n_heuristic] = findReward(machine, role, state);
					for (int i = 0; i < vstate.length; i++) {
						vstate[i] += 1e-8 * (Math.random() - 0.5);
					}
					nstep++;
					state = machine.getRandomNextState(state);
					states.add(vstate);
					pstates.add(pstate);
				}
				double eval = findReward(machine, role, state);
				int randomIndex = (int) (Math.random() * pstates.size());
				PropNetMachineState randomState = pstates.get(randomIndex);
				double randomEval = findReward(machine.internalDC(randomState));
				synchronized (heuristicRegression) {
					for (double[] s : states) {
						heuristicRegression.addObservation(s, eval);
					}
					dcRegression.addData(randomEval, eval);
				}
			}
		}
	}

	public double heuristic(MachineState state) {
		if (heuristics == null) return 50;
		double reward = findReward(mainThreadMachine, player.getRole(), state);
		double heuristic = heuristic_yint + reward * heuristic_goalweight;
		PropNetMachineState pnstate = (PropNetMachineState) state;
		for (int i = 0; i < heuristics.length; i++) {
			if (pnstate.props[i]) heuristic += heuristics[i];
		}
		if (heuristic < MyPlayer.MIN_SCORE) heuristic = MyPlayer.MIN_SCORE;
		if (heuristic > MyPlayer.MAX_SCORE) heuristic = MyPlayer.MAX_SCORE;
		return heuristic;
	}

	public void multiPlayerMetaGame(long timeout)
			throws MoveDefinitionException, TransitionDefinitionException {
		Role role = player.getRole();
		List<MetaGameDCThread> pool = new ArrayList<>();
		int n_thread = MyPlayer.N_THREADS;

		Log.println("begin random exploration...");
		for (int i = 0; i < n_thread; i++) {
			MetaGameDCThread thread = new MetaGameDCThread(machines[i], role, timeout);
			pool.add(thread);
			thread.start();
		}
		for (int i = 0; i < n_thread; i++) {
			try {
				pool.get(i).join();
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
		List<Integer> canUseHeuristic = new ArrayList<>();
		canUseHeuristic.add(0);
		canUseHeuristic.add(1 + heuristicNames.size()); // goal
		for (int i = 0; i < heuristicNames.size(); i++) {
			double sum = 0;
			for (MetaGameDCThread thread : pool) {
				sum += thread.timeCalc[i].getSlope();
			}
			Log.println(heuristicNames.get(i) + " time correlation: " + sum / 4);
			if (sum < 0) canUseHeuristic.add(i + 1);
		}

		Log.println("states explored: " + heuristicRegression.getN());

		int[] canUseArr = new int[canUseHeuristic.size()];
		for (int i = 0; i < canUseHeuristic.size(); i++) {
			canUseArr[i] = canUseHeuristic.get(i);
		}

		int nbase = smthread.m.props.size();
		heuristic_yint = 0;
		heuristics = new double[nbase];
		RegressionResults results = heuristicRegression.regress(canUseArr);
		for (int j = 0; j < canUseArr.length; j++) {
			double est = results.getParameterEstimate(j);
			if (!Double.isFinite(est)) est = 0;
			int i = canUseArr[j];
			if (i == 0) Log.printf("\tintercept : %.3f\n", heuristic_yint = est);
			else if (i > heuristicNames.size()) {
				Log.printf("\tgoal : %.3f\n", heuristic_goalweight = est);
			} else {
				for (int k : heuristicProps.get(i - 1)) {
					heuristics[k] += est;
				}
				Log.printf("\t%s : %.3f\n", heuristicNames.get(i - 1), est);
			}
		}

		double heuristicRsq = results.getAdjustedRSquared();
		Log.println("heuristic rsq: " + heuristicRsq);
		double dcRsq = dcRegression.getRSquare();
		Log.println("depth charge rsq: " + dcRsq);
		heuristicWeight = heuristicRsq / dcRsq;
		if (heuristicWeight < 0 || !Double.isFinite(heuristicWeight)) {
			heuristicWeight = 0;
		}
		Log.println("heuristic weight: " + heuristicWeight);
		exploration_bias = EXPLORATION_BIAS_FACTOR * Math.sqrt(1 + heuristicWeight);
		Log.println("exploration bias: " + exploration_bias);
	}

	private int findReward(int[] rewards) {
		if (opponents.size() == 0) return rewards[ourRoleIndex];
		double reward = OUR_WEIGHT * rewards[ourRoleIndex];
		for (int i = 0; i < roles.length; i++) {
			if (i == ourRoleIndex) continue;
			reward += (MyPlayer.MAX_SCORE - rewards[i]) * oppWeight;
		}
		return (int) Math.round(reward);
	}

	private int findReward(StateMachine machine, Role role, MachineState state) {
		try {
			if (opponents.size() == 0) return machine.findReward(role, state);
			double reward = OUR_WEIGHT * machine.findReward(role, state);
			for (Role opp : opponents) {
				reward += (MyPlayer.MAX_SCORE - machine.findReward(opp, state)) * oppWeight;
			}
			return (int) Math.round(reward);
		} catch (GoalDefinitionException e) {
			return 0;
		}
	}

	@Override
	public Move run(StateMachine machine, MachineState rootstate, Role role, List<Move> moves,
			long timeout) throws GoalDefinitionException, MoveDefinitionException,
					TransitionDefinitionException {

		if (solution != null && !solution.isEmpty()) {
			Move move = solution.pop();
			Log.println("solution move: " + move);
			if (moves.contains(move)) return move;
			else { // solver went awry
				Log.println("solver error: move " + move + " is illegal");
				solution = null;
			}
		}

		Log.println("--------------------");

		if (checkStateMachineStatus()) {
			// reinit state machine
			machine = player.getStateMachine();
			rootstate = player.getCurrentState();
		}

		mainThreadMachine = machine;

		return run_(machine, rootstate, role, moves, timeout);
	}

	public Move run_(StateMachine machine, MachineState rootstate, Role role, List<Move> moves,
			long timeout) throws GoalDefinitionException, MoveDefinitionException,
					TransitionDefinitionException {
		// we don't cache anyway. might as well...
		if (moves.size() == 1) {
			Log.println("one legal move: " + moves.get(0));
			return moves.get(0);
		}
		Log.println("threads running: " + Thread.activeCount());
		Map<Role, Set<Move>> oldUseless = null;
		Log.println("number of legal moves: " + moves.size());
		ignoreProps = null;
		if (propNetInitialized) {
			oldUseless = new HashMap<>();
			List<Proposition> bases = smthread.m.props;
			ignoreProps = new boolean[bases.size()];
			for (Role r : machine.findRoles()) {
				oldUseless.put(r, new HashSet<>(useless.get(r)));
			}
			Set<Component> reachableBases = new HashSet<>();
			Set<Component> reachableBasesBackwards = new HashSet<>();
			Map<GdlSentence, Proposition> propMap = smthread.m.p.getInputPropositions();
			for (Move move : moves) {
				Component c = propMap.get(ProverQueryBuilder.toDoes(role, move));
				findComponentsForwards(c, reachableBases);
				c = smthread.m.p.getLegalInputMap().get(c);
				findComponentsBackwards(c, reachableBasesBackwards);
			}
			reachableBases.addAll(reachableBasesBackwards);
			reachableBases.retainAll(new HashSet<>(bases));
			Log.printf("%d of %d props relevant\n", reachableBases.size(), bases.size());
			int count = 0;
			Set<Component> ignore = new HashSet<>();
			Set<Component> relevant = new HashSet<>();
			for (Component c : reachableBases) {
				findComponentsBackwards(c, relevant);
			}
			for (Role r : machine.findRoles()) {
				for (Move action : machine.findActions(r)) {
					Component does = propMap.get(ProverQueryBuilder.toDoes(r, action));
					if (does == null) continue;
					findComponentsForwards(does, ignore);
					if (!relevant.contains(does)) {
						useless.get(r).add(action);
						count++;
					}
				}
			}
			Log.println("found " + count + " locally irrelevant inputs");
			ignore.removeAll(reachableBases);
			count = 0;
			for (int i = 0; i < bases.size(); i++) {
				if (ignore.contains(bases.get(i))) {
					count++;
					ignoreProps[i] = true;
				}
			}
			Log.println("found " + count + " constant propositions");
		}

		long timestart = System.currentTimeMillis();

		int nthread = MyPlayer.N_THREADS - 1;
		if (!propNetInitialized) nthread--;
		Log.println("depth charge threads: " + nthread);

		// set up tree

		dagMap = new HashMap<>();

		root = new MTreeNode(rootstate);
		dagMap.put(rootstate, root);

		DepthChargeThread[] threads = new DepthChargeThread[nthread];
		ArrayBlockingQueue<Stack<MTreeNode>> input = new ArrayBlockingQueue<>(1);

		BlockingQueue<DCOut> output = new LinkedBlockingQueue<>();
		for (int i = 0; i < nthread; i++) {
			threads[i] = new DepthChargeThread(machines[i], role, timeout, input, output);
			threads[i].start();
		}
		int[] timers = new int[3];

		while (System.currentTimeMillis() < timeout) {
			if (root.isLooselyProven()) break;
			timers[0] -= System.currentTimeMillis();
			Stack<MTreeNode> tree = select(root);
			timers[0] += System.currentTimeMillis();
			MTreeNode node = tree.peek();
			if (node.isMaxNode() && machine.isTerminal(node.state)) {
				timers[2] -= System.currentTimeMillis();
				double reward = findReward(machine, role, node.state);
				backpropogate(tree, reward, reward * reward, true, true);
				timers[2] += System.currentTimeMillis();
			} else {
				// EXPLORE
				timers[1] -= System.currentTimeMillis();
				if (!input.offer(tree)) {
					timers[1] += System.currentTimeMillis();
					timers[2] -= System.currentTimeMillis();
					backpropogate(tree, 0, 0, false, false);
					timers[2] += System.currentTimeMillis();
				} else timers[1] += System.currentTimeMillis();
				// BACKPROP
				timers[2] -= System.currentTimeMillis();
				while (true) {
					DCOut out = output.poll();
					if (out == null) break;
					if (out.eval == FAIL) continue;
					backpropogate(out.node, out.eval, out.avgsq, false, true);
				}
				timers[2] += System.currentTimeMillis();
			}
		}
		sanitizeMoves(role, root, moves);
		Collections.sort(root.children);
		for (MTreeNode child : root.children) {
			Log.printf(
					"v=(%d, %d) s=(%.1f, %.1f, %.1f) b=(%.0f, %.0f) d=%d %s\n",
					child.visits,
					child.heuristicVisits - child.visits / depthChargesPerState,
					child.sum_utility / child.visits, child.heuristic,
					child.utility(),
					child.lower, child.upper, child.depth, child.move);
		}
		MTreeNode bestChild = root.children.get(root.children.size() - 1);
		Log.printf("played=%s visits=%d/%d depth=%d\n",
				bestChild.move, bestChild.visits,
				root.visits, root.depth);
		long elapsed_time = (System.currentTimeMillis() - timestart);
		Log.printf("time=%d breakdown=%s\n", elapsed_time,
				Arrays.toString(timers));

		input.clear();
		long totalTimeWaiting = 0;
		for (DepthChargeThread thread : threads) {
			totalTimeWaiting += thread.timeSpentWaiting;
		}

		Log.println("depth charge inactive time: " + totalTimeWaiting + " ms");
		double factor = (double) totalTimeWaiting / (elapsed_time * threads.length);
		factor = 1 / (1 - factor);
		if (System.currentTimeMillis() >= timeout && factor >= 2) {
			Log.printf("depth charges too slow. now doing %d per state\n",
					depthChargesPerState *= factor);
		}

		root = null; // allow gc

		Move chosen = bestChild.move;
		if (chosen == USELESS_MOVE) {
			int leastUseful = Integer.MAX_VALUE;
			for (Move move : moves) {
				if (!useless.get(role).contains(move)) continue;
				int usefulness = 0;
				for (List<Move> jmove : machine.getLegalJointMoves(
						rootstate, role, move)) {
					PropNetMachineState next = (PropNetMachineState) machine.getNextState(
							rootstate, jmove);
					PropNetMachineState state = (PropNetMachineState) rootstate;
					for (int i = 0; i < next.props.length; i++) {
						if (next.props[i] != state.props[i]) usefulness++;
					}
				}
				if (usefulness < leastUseful) {
					leastUseful = usefulness;
					chosen = move;
				}
			}
			Log.println("noop chosen. playing most useless move: " + chosen);
		}

		if (oldUseless != null) useless = oldUseless;
		return chosen;
	}

	private void sanitizeMoves(Role role, MTreeNode root, Collection<Move> legal) {
		MTreeNode remove = null;
		for (MTreeNode child : root.children) {
			if (!legal.contains(child.move)) {
				Set<Move> uselessMoves = useless.get(role);
				uselessMoves.retainAll(legal);
				if (uselessMoves.size() > 0) child.move = USELESS_MOVE;
				else remove = child;
			}
		}
		if (remove != null) root.children.remove(remove);
	}

	private Stack<MTreeNode> select(MTreeNode node) throws TransitionDefinitionException {
		Stack<MTreeNode> out = new Stack<>();
		while (true) {
			if (node == null) {
				for (MTreeNode n : out) {
					System.out.printf("%s\t%s\t%s\t(%.0f, %.0f)\t",
							n.move, n.visits, n.depth, n.lower, n.upper);
					for (MTreeNode c : n.children) {
						System.out.print(c.score(n.isMaxNode() ? 1 : -1, n) + " ");
					}
					System.out.println();
				}
				System.out.flush();
			}
			out.push(node);
			node = node.selectBestChild();
			if (node == null) return out;
		}
	}

	private List<Move> getUsefulMoves(StateMachine machine, Role role, MachineState state) {
		List<Move> actions = null;
		try {
			actions = machine.findLegals(role, state);
		} catch (MoveDefinitionException e) {
			e.printStackTrace();
		}
		if (!propNetInitialized || !USE_MULTIPLAYER_FACTORING) return actions;
		Set<Move> uselessMoves = useless.get(role);

		List<Move> output = new ArrayList<>();
		Move uselessMove = null;
		for (Move move : actions) {
			if (uselessMoves.contains(move)) {
				uselessMove = move;
				continue;
			}
			output.add(move);
		}
		if (uselessMove != null) output.add(null);
		return output;
	}

	private void propagateBound(MTreeNode node) {
		if (!node.setBounds()) return;
		for (MTreeNode parent : node.parents) {
			propagateBound(parent);
		}
	}

	private void backpropogate(Stack<MTreeNode> stack, double eval, double avgsq,
			boolean proven, boolean isScore) throws TransitionDefinitionException {
		int index = stack.size() - 1;
		MTreeNode node = stack.get(index--);
		if (proven) {
			node.lower = node.upper = eval;
			for (MTreeNode parent : node.parents) {
				propagateBound(parent);
			}
		}
		Queue<MTreeNode> q = new ArrayDeque<>();
		q.add(node);
		int depth = stack.size() / 2;
		Set<MTreeNode> visited = new HashSet<>();
		while (!q.isEmpty()) {
			node = q.poll();
			node.addData(eval, avgsq, depth, isScore);
			for (MTreeNode parent : node.parents) {
				if (visited.contains(parent)) continue;
				visited.add(parent);
				if (index >= 0 && parent == stack.get(index)) {
					index--;
					q.add(parent);
				} else if (parent.bestChildCached == node) {
					q.add(parent);
				}
			}
		}
	}

	@Override
	public void cleanUp() {
		if (smthread.isAlive()) {
			smthread.m.kill = true;
			try {
				smthread.join();
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
	}

	private class LazyExpander {
		private int index = -1;
		private MTreeNode node;
		private List<List<Move>> allMoves;
		private List<Move> moves;
		private int maxIndex = 1;

		public LazyExpander(MTreeNode node) {
			this.node = node;
			if (node.isMaxNode()) {
				moves = getUsefulMoves(mainThreadMachine, roles[ourRoleIndex], node.state);
				maxIndex = moves.size();
			} else {
				allMoves = new ArrayList<>();
				for (int i = 0; i < roles.length; i++) {
					if (i == ourRoleIndex) {
						allMoves.add(null);
					} else {
						List<Move> moves = getUsefulMoves(mainThreadMachine, roles[i], node.state);
						allMoves.add(moves);
						maxIndex *= moves.size();
					}
				}
			}
		}

		public MTreeNode next() throws TransitionDefinitionException {
			if (++index == maxIndex) return null;
			if (node.isMaxNode()) {
				Move move = moves.get(index);
				MTreeNode newnode = new MTreeNode(node.state, move, node);
				node.children.add(newnode);
				return newnode;
			} else {
				List<Move> jmove = new ArrayList<>();
				int copyIndex = index;
				for (int i = 0; i < roles.length; i++) {
					if (i == ourRoleIndex) jmove.add(node.move);
					else {
						List<Move> curMoves = allMoves.get(i);
						jmove.add(curMoves.get(copyIndex % curMoves.size()));
						copyIndex /= curMoves.size();
					}
				}
				MachineState newstate = mainThreadMachine.findNext(jmove, node.state);
				if (propNetInitialized) {
					PropNetMachineState oldstate = (PropNetMachineState) node.state;
					PropNetMachineState newpstate = (PropNetMachineState) newstate;
					for (int i = 0; i < ignoreProps.length; i++) {
						if (ignoreProps[i]) newpstate.props[i] = oldstate.props[i];
					}
				}
				MTreeNode newnode;
				if (dagMap.containsKey(newstate)) {
					newnode = dagMap.get(newstate);
					newnode.parents.add(node);
				} else {
					newnode = new MTreeNode(newstate, node);
					dagMap.put(newstate, newnode);
				}
				node.children.add(newnode);
				return newnode;
			}
		}
	}

	private class DepthChargeThread extends Thread {

		private StateMachine machine;
		private Role role;
		private long timeout;
		private BlockingQueue<Stack<MTreeNode>> input;
		private BlockingQueue<DCOut> output;
		private int timeSpentWaiting;

		public DepthChargeThread(StateMachine machine, Role role, long timeout,
				BlockingQueue<Stack<MTreeNode>> input2, BlockingQueue<DCOut> output) {
			this.machine = machine;
			this.role = role;
			this.timeout = timeout;
			this.input = input2;
			this.output = output;
		}

		private DCOut averageSimulate(Stack<MTreeNode> tree) throws MoveDefinitionException,
				TransitionDefinitionException, GoalDefinitionException {
			double total = 0;
			double sumsq = 0;
			for (int i = 0; i < depthChargesPerState; i++) {
				double next = simulate(tree);
				if (next == FAIL) return new DCOut(tree, FAIL, 0);
				total += next;
				sumsq += next * next;
			}
			total /= depthChargesPerState;
			sumsq /= depthChargesPerState;
			return new DCOut(tree, total, sumsq);
		}

		private double simulate(Stack<MTreeNode> tree) throws MoveDefinitionException,
				TransitionDefinitionException, GoalDefinitionException {
			MTreeNode node = tree.peek();
			MachineState state = node.state;
			if (node.move != null) state = machine.getRandomNextState(state, role, node.move);
			double score;
			if (propNetInitialized) {
				JustKiddingPropNetStateMachine pnsm = (JustKiddingPropNetStateMachine) machine;
				score = findReward(pnsm.internalDC((PropNetMachineState) state));
			} else {
				while (!machine.isTerminal(state)) {
					if (System.currentTimeMillis() > timeout) return FAIL;
					state = machine.getRandomNextState(state);
				}
				score = findReward(machine, role, state);
			}
			return score;
		}

		@Override
		public void run() {
			try {
				while (true) {
					Stack<MTreeNode> tree = input.poll();
					if (tree == null) {
						long start = System.currentTimeMillis();
						tree = input.poll(
								timeout - System.currentTimeMillis() + MyPlayer.TIMEOUT_BUFFER,
								TimeUnit.MILLISECONDS);
						if (tree == null) return;
						timeSpentWaiting += System.currentTimeMillis() - start;
					}
					output.offer(averageSimulate(tree));
				}
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
	}

	private static final int MTREENODE_PRIOR_VISITS = 2;
	private static final double MTREENODE_PRIOR_UTIL = 100;
	private static final double MTREENODE_PRIOR_SUMSQ = 10000;

	private class MTreeNode implements Comparable<MTreeNode> {
		// prior: sum squares = 10000 so that stdev != 0
		public int heuristicVisits = MTREENODE_PRIOR_VISITS;
		public int visits = MTREENODE_PRIOR_VISITS;
		public double sum_utility = MTREENODE_PRIOR_UTIL;
		public double sum_sq = MTREENODE_PRIOR_SUMSQ;
		// bounds
		public double lower = MyPlayer.MIN_SCORE;
		public double upper = MyPlayer.MAX_SCORE;
		public List<MTreeNode> children = new ArrayList<>();
		public List<MTreeNode> parents = new ArrayList<>();

		public MachineState state;
		public Move move; // null if max-node; non-null if min-node

		public int depth = 0;
		public boolean isMaxNode;
		private MTreeNode bestChildCached = null;

		protected double heuristic;
		private LazyExpander expander;
		private boolean first = true;

		private void init(MachineState state, MTreeNode parent, boolean isMaxNode) {
			this.state = state;
			this.heuristic = heuristic(state);
			this.isMaxNode = isMaxNode;
			if (parent != null) this.parents.add(parent);
		}

		public MTreeNode(MachineState state) {
			init(state, null, true);
		}

		public MTreeNode(MachineState state, MTreeNode parent) {
			init(state, parent, true);
		}

		public MTreeNode(MachineState state, Move move, MTreeNode parent) {
			this.move = move;
			init(state, parent, false);
		}

		public int compareTo(MTreeNode other) {
			if (other == null) return 1;
			int cmp = Double.compare(utility(), other.utility());
			if (cmp != 0) return cmp;
			cmp = Double.compare(lower, other.lower);
			if (cmp != 0) return cmp;
			cmp = Double.compare(upper, other.upper);
			if (cmp != 0) return cmp;
			return Double.compare(visits, other.visits);
		}

		public boolean setBounds() {
			assert!children.isEmpty();
			double oldupp = upper, oldlow = lower, oldH = heuristic;
			if (isMaxNode()) {
				upper = MyPlayer.MIN_SCORE;
				lower = MyPlayer.MIN_SCORE;
				heuristic = MyPlayer.MIN_SCORE;
				for (MTreeNode c : children) {
					upper = Math.max(upper, c.upper);
					lower = Math.max(lower, c.lower);
					heuristic = Math.max(heuristic, c.heuristic);
				}
				assert expander == null;
			} else {
				upper = MyPlayer.MAX_SCORE;
				lower = MyPlayer.MAX_SCORE;
				heuristic = MyPlayer.MAX_SCORE;
				for (MTreeNode c : children) {
					upper = Math.min(upper, c.upper);
					lower = Math.min(lower, c.lower);
					heuristic = Math.min(heuristic, c.heuristic);
				}
				if (expander != null) lower = oldlow;
			}

			heuristic = putInBounds(heuristic);
			return upper != oldupp || lower != oldlow || heuristic != oldH;
		}

		public double putInBounds(double eval) {
			if (eval < lower) eval = lower;
			if (eval > upper) eval = upper;
			return eval;
		}

		public boolean isProven() {
			return lower == upper;
		}

		// returns whether the best move is known
		// (even if its evaluation is not)
		public boolean isLooselyProven() {
			assert isMaxNode;
			if (isProven()) return true;
			if (children.isEmpty()) return false;
			if (expander != null) return false;
			MTreeNode bestChild = children.get(0);
			MTreeNode visitsChild = bestChild;
			for (MTreeNode child : children) {
				if (child.lower > bestChild.lower
						|| (child.lower == bestChild.lower && child.upper > bestChild.upper)) {
					bestChild = child;
				}
				if (child.visits > visitsChild.visits) visitsChild = child;
			}
			if (bestChild != visitsChild) return false;
			for (MTreeNode child : children) {
				if (child != bestChild && child.upper > bestChild.lower) return false;
			}
			return true;
		}

		public boolean isMaxNode() {
			return isMaxNode;
		}

		public double utility() {
			return putInBounds(score(0, root));
		}

		// dynamic score: multiplies by standard deviation
		public double score(double c, MTreeNode parent) {
			double heuristicEffVisits = heuristicWeight * visits
					* parent.heuristicVisits / parent.visits;
			double eff_sum = sum_utility + heuristic * heuristicEffVisits;
			double eff_visits = visits + heuristicEffVisits;
			double eff_sumsq = sum_sq + 100 * heuristic * heuristicEffVisits;

			double util = eff_sum / eff_visits;
			double var = eff_sumsq / eff_visits - util * util;

			eff_visits -= (1 + heuristicWeight);
			var = c * Math.sqrt(Math.log(parent.visits) / eff_visits * var);
			return util + var;
		}

		public void addData(double eval, double avgsq, int newDepth, boolean isScore) {
			if (isScore) {
				visits += depthChargesPerState;
				sum_utility += eval * depthChargesPerState;
				sum_sq += avgsq * depthChargesPerState;
				depth = Math.max(depth, newDepth);
			}
			heuristicVisits++;
		}

		public MTreeNode selectBestChild() throws TransitionDefinitionException {
			if (first) {
				first = false;
				return null;
			}
			if (expander == null && children.isEmpty()) {
				expander = new LazyExpander(this);
			}
			while (expander != null) {
				MTreeNode next = expander.next();
				if (next == null) {
					expander = null;
					propagateBound(this);
				} else if (!next.isProven()) return bestChildCached = next;
			}

			MTreeNode best = null;
			int countBest = 1;
			if (isMaxNode()) {
				double score = Double.NEGATIVE_INFINITY;
				for (MTreeNode child : children) {
					if (child.isProven()) continue;
					double newscore = child.score(exploration_bias, this);
					if (newscore > score) {
						score = newscore;
						best = child;
						countBest = 1;
					} else if (newscore == score) {
						if (Math.random() < 1.0 / (++countBest)) {
							best = child;
						}
					}
				}
			} else {
				double score = Double.POSITIVE_INFINITY;
				for (MTreeNode child : children) {
					if (child.isProven()) continue;
					double newscore = child.score(-exploration_bias, this);
					if (newscore < score) {
						score = newscore;
						best = child;
						countBest = 1;
					} else if (newscore == score) {
						if (Math.random() < 1.0 / (++countBest)) {
							best = child;
						}
					}
				}
			}
			return bestChildCached = best;
		}
	}

	private static class DCOut {
		public double eval;
		public double avgsq;
		public Stack<MTreeNode> node;

		public DCOut(Stack<MTreeNode> node, double eval, double avgsq) {
			this.eval = eval;
			this.node = node;
			this.avgsq = avgsq;
		}
	}

	private void findComponentsBackwards(Collection<Component> current, Set<Component> visited) {
		for (Component c : current) {
			findComponentsBackwards(c, visited);
		}
	}

	private void findComponentsBackwards(Component current, Set<Component> visited) {
		Queue<Component> queue = new LinkedList<>();
		queue.add(current);
		while (!queue.isEmpty()) {
			current = queue.poll();
			if (visited.contains(current)) continue;
			visited.add(current);
			if (inputToLegalMap.containsKey(current)) current = inputToLegalMap.get(current);
			for (Component parent : current.getInputs()) {
				queue.offer(parent);
			}
		}
	}

	private void findComponentsForwards(Component current, Set<Component> visited) {
		Queue<Component> queue = new LinkedList<>();
		queue.add(current);
		while (!queue.isEmpty()) {
			current = queue.poll();
			if (visited.contains(current)) continue;
			visited.add(current);
			if (legalToInputMap.containsKey(current)) current = legalToInputMap.get(current);
			for (Component next : current.getOutputs()) {
				queue.offer(next);
			}
		}
	}

	private class StateMachineCreatorThread extends Thread {
		private List<Gdl> description;
		private Role role;
		public JustKiddingPropNetStateMachine m;
		public Set<Component> reachable;

		public StateMachineCreatorThread(Role role, List<Gdl> description) {
			this.role = role;
			this.description = description;
		}

		@Override
		public void run() {
			m = new JustKiddingPropNetStateMachine();
			m.initialize(description);
			if (m.kill) {
				Log.println("propnet building aborted");
				return;
			}
			Log.println("propnet created. processing...");

			// make two-way input maps
			Map<GdlSentence, Proposition> inputs = m.p.getInputPropositions();
			Collection<Proposition> values = inputs.values();
			legalToInputMap = new HashMap<>(m.p.getLegalInputMap());
			inputToLegalMap = new HashMap<>(m.p.getLegalInputMap());
			for (Proposition value : values) {
				legalToInputMap.remove(value);
				inputToLegalMap.remove(inputToLegalMap.get(value));
			}

			reachable = new HashSet<>();
			findComponentsBackwards(m.p.getTerminalProposition(), reachable);
			Set<Component> goals = new HashSet<>();
			goals.addAll(m.p.getGoalPropositions().get(role));
			Set<Component> badInputSet = new HashSet<>(inputs.values());
			findComponentsBackwards(goals, reachable);
			for (Component comp : reachable) {
				badInputSet.remove(comp);
			}
			int count = 0;

			for (GdlSentence input : inputs.keySet()) {
				if (badInputSet.contains(inputs.get(input))) {
					Role role = Role.create(input.get(0).toString());
					Move move = Move.create(input.get(1).toString());
					useless.get(role).add(move);
					count++;
				}
			}
			Map<Role, Set<Proposition>> nLegals = m.p.getLegalPropositions();
			nUsefulRoles = nLegals.size();
			for (Role role : useless.keySet()) {
				if (useless.get(role).size() == nLegals.get(role).size()) {
					Log.println("role " + role + " is irrelevant");
					nUsefulRoles--;
				}
			}
			if (nUsefulRoles == 0) Log.println("this is a 0-player game...");
			Log.println("found " + count + " irrelevant inputs");

			Map<String, Integer> heuristicMap = new HashMap<>();
			heuristicProps = new ArrayList<>();
			heuristicNames = new ArrayList<>();
			// find heurisitics
			for (int i = 0; i < m.props.size(); i++) {
				GdlSentence base = m.props.get(i).getName().get(0).toSentence();
				if (base.arity() != 3) continue;
				String name = base.getBody().subList(2, base.arity()).toString();
				if (!heuristicMap.containsKey(name)) {
					heuristicMap.put(name, heuristicProps.size());
					heuristicNames.add(name);
					heuristicProps.add(new ArrayList<>());
				}
				heuristicProps.get(heuristicMap.get(name)).add(i);

			}
			heuristicRegression = new MillerUpdatingRegression(1 + heuristicNames.size(), true);
			dcRegression = new SimpleRegression();

			Log.println("propnet ready");
		}
	}

	// a namespace for astar-related methods...or really just a DFS
	private class DFSSolver extends Solver {

		private boolean[] ignoreProps;
		private BlockingQueue<Solver> out;
		private long timeout;
		private int id;
		private StateMachine machine;

		@Override
		public String toString() {
			return "solver-" + id;
		}

		public DFSSolver(StateMachine machine, long timeout, boolean[] ignoreProps,
				BlockingQueue<Solver> out, int id) {
			this.machine = machine;
			this.timeout = timeout;
			this.ignoreProps = ignoreProps;
			this.out = out;
			this.id = id;
		}

		private int compare(MachineState state1, MachineState state2) {
			boolean[] props1 = ((PropNetMachineState) state1).props;
			boolean[] props2 = ((PropNetMachineState) state2).props;
			for (int i = 0; i < props1.length; i++) {
				if (props1[i] == props2[i] || ignoreProps[i]) continue;
				return props1[i] ? 1 : -1;
			}
			return 0;
		}

		private class StateInfo {
			public MachineState parent;
			public Move parentMove;
			public int distance;

			public StateInfo(MachineState parent, Move parentMove, int distance) {
				this.parent = parent;
				this.parentMove = parentMove;
				this.distance = distance;
			}
		}

		private class PQEntry implements Comparable<PQEntry> {
			public MachineState state;
			public int value;

			public PQEntry(MachineState state, int value) {
				this.state = state;
				this.value = value;
			}

			public int compareTo(PQEntry other) {
				return Integer.compare(value, other.value);
			}
		}

		private Stack<Move> reconstruct(Map<MachineState, StateInfo> info, MachineState state) {
			Stack<Move> stack = new Stack<>();
			while (state != null) {
				StateInfo i = info.get(state);
				stack.push(i.parentMove);
				state = i.parent;
			}
			stack.pop();
			return stack;
		}

		@Override
		public void run() {
			try {
				solve();
			} catch (Exception e) {
				e.printStackTrace();
			}
			out.add(this);
		}

		// psuedocode from Wikipedia on A*
		public void solve() throws GoalDefinitionException, MoveDefinitionException,
				TransitionDefinitionException {
			Role role = player.getRole();
			MachineState initial = machine.getInitialState();
			Set<MachineState> closed = new TreeSet<>(this::compare);
			Map<MachineState, StateInfo> info = new TreeMap<>(this::compare);

			PriorityQueue<PQEntry> pq = new PriorityQueue<>();
			pq.add(new PQEntry(initial, 0));
			info.put(initial, new StateInfo(null, null, 0));
			best_reward = 0;
			best = null;

			while (!pq.isEmpty()) {
				if (System.currentTimeMillis() > timeout || kill) {
					best = null;
					return;
				}
				MachineState u = pq.poll().state;
				if (closed.contains(u)) continue;
				closed.add(u);
				if (machine.isTerminal(u)) {
					int reward = machine.findReward(role, u);
					if (reward > best_reward) {
						best = reconstruct(info, u);
						best_reward = reward;
						if (best_reward == MyPlayer.MAX_SCORE) return;
					}
				}
				int newDist = info.get(u).distance + 1;
				for (Move move : machine.getLegalMoves(u, role)) {
					MachineState v = machine.getRandomNextState(u, role, move);
					StateInfo vinfo = info.get(v);
					if (vinfo == null) {
						info.put(v, new StateInfo(u, move, newDist));
						pq.add(new PQEntry(v, newDist));
					} else if (!closed.contains(u) && vinfo.distance > newDist) {
						vinfo.distance = newDist;
						vinfo.parent = u;
						vinfo.parentMove = move;
						pq.add(new PQEntry(v, newDist));
					}
				}
			}
		}
	}
}