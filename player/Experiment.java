import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
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

import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
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
	private static final double CFACTOR = 1.0;
	private StateMachine[] machines;
	private boolean propNetInitialized = false;
	private MyPlayer player;

	private StateMachineCreatorThread smthread;

	// communication between metagame threads
	private Stack<Move> solution;
	private Map<Role, Set<Move>> useless;
	private Map<Role, Move> noops;
	private List<Role> opponents;
	private Map<Proposition, Proposition> legalToInputMap;
	private Map<Proposition, Proposition> inputToLegalMap;
	private int nUsefulRoles;
	private boolean[] ignoreProps;

	// for timeout control
	private List<MachineState> nextPossibles;
	private int nBehindServer;

	// for weighted depth charge results
	private static final double OUR_WEIGHT = 2. / 3;
	private double oppWeight;
	private Role[] roles;
	private int ourRoleIndex = -1;

	// heuristics
	// GdlTerm --> index into heuristicCalcs
	private Map<GdlTerm, Integer> heuristicMap;
	private List<LinRegCalc> heuristicCalcs;
	private double heuristic_yint;
	private double[] heuristics;
	// for each heuristic in heuristicCalcs, contains the props that affect
	private List<List<Integer>> heuristicProps;

	private boolean checkStateMachineStatus() {
		if (!propNetInitialized && !smthread.isAlive()) {
			player.switchToNewPropnets(smthread.m, machines);
			Log.println("propnets initialized");
			return propNetInitialized = true;
		}
		return false;
	}

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

	public void gc() {
		long start = System.currentTimeMillis();
		System.gc();
		Log.println("garbage collection: " + (System.currentTimeMillis() - start) + " ms");
	}

	@Override
	public void metaGame(StateMachineGamer gamer, long timeout) {
		gc();

		useless = new HashMap<>();
		noops = new HashMap<>();
		solution = null;
		opponents = new ArrayList<>();
		nextPossibles = null;
		nBehindServer = 1;
		heuristics = null;

		Set<GdlConstant> all = new HashSet<>();
		Set<GdlConstant> impossibles = new HashSet<>();

		StateMachine machine = gamer.getStateMachine();
		roles = machine.findRoles().toArray(new Role[0]);
		for (int i = 0; i < roles.length; i++) {
			Role role = roles[i];
			if (!role.equals(gamer.getRole())) opponents.add(role);
			else ourRoleIndex = i;
			useless.put(role, new HashSet<>());
		}
		Log.println("roles: " + Arrays.toString(roles) + " | our role: " + ourRoleIndex);
		oppWeight = opponents.size() == 0 ? 0 : (1 - OUR_WEIGHT) / opponents.size();

		// find clock
		while (System.currentTimeMillis() < timeout && smthread.isAlive()) {
			Map<GdlConstant, Set<GdlSentence>> possibles = new HashMap<>();
			MachineState state = machine.getInitialState();
			while (!machine.isTerminal(state) && System.currentTimeMillis() < timeout) {
				for (GdlSentence sent : state.getContents()) {
					sent = sent.get(0).toSentence();
					GdlConstant name = sent.getName();
					if (impossibles.contains(name)) continue;
					if (!possibles.containsKey(name)) {
						possibles.put(name, new HashSet<>());
						all.add(name);
					}
					Set<GdlSentence> previous = possibles.get(name);
					if (previous.contains(sent)) {
						impossibles.add(name);
						possibles.remove(name);
						Log.println(name + " is not the clock");
					} else previous.add(sent);
				}
				try {
					state = machine.getRandomNextState(state);
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		}

		if (!checkStateMachineStatus()) {
			Log.println("still building propnet...");
			return;
		}

		for (Role r : machine.getRoles()) {
			Log.println("noop for role " + r + " is " + noops.get(r));
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
		all.removeAll(impossibles);
		if (all.size() == 0) Log.println("no clock");
		else if (all.size() > 1) Log.println("too many possible clocks: " + all);
		else {
			GdlConstant clockConstant = all.iterator().next();
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

	private class MetaGameDCOut {
		double[] counts = new double[heuristicCalcs.size()];
		double eval;
	}

	private class MetaGameDCThread extends Thread {

		private JustKiddingPropNetStateMachine machine;
		private long timeout;
		private Role role;
		public LinRegCalc[] timeCalc = new LinRegCalc[heuristicCalcs.size()];
		public List<MetaGameDCOut> output = new ArrayList<>();

		public MetaGameDCThread(StateMachine machine, Role role, long timeout) {
			this.machine = (JustKiddingPropNetStateMachine) machine;
			this.role = role;
			this.timeout = timeout;
			for (int i = 0; i < timeCalc.length; i++) {
				timeCalc[i] = new LinRegCalc(heuristicCalcs.get(i).term);
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
			int n_heuristic = heuristicCalcs.size();
			while (System.currentTimeMillis() < timeout) {
				MetaGameDCOut out = new MetaGameDCOut();
				MachineState state = initial;
				int nstep = 0;
				while (!machine.isTerminal(state)) {
					if (System.currentTimeMillis() > timeout) return;
					PropNetMachineState pstate = (PropNetMachineState) state;
					for (int i = 0; i < n_heuristic; i++) {
						int icount = 0;
						for (int j : heuristicProps.get(i)) {
							if (pstate.props[j]) {
								out.counts[i]++;
								icount++;
							}
						}
						timeCalc[i].addData(nstep, icount);
					}
					nstep++;
					state = machine.getRandomNextState(state);
				}
				for (int i = 0; i < n_heuristic; i++) {
					out.counts[i] /= nstep;
				}
				out.eval = findReward(machine, role, state);
				output.add(out);
			}
		}
	}

	public double heuristic(MachineState state) {
		if (heuristics == null) return 50;
		double heuristic = heuristic_yint;
		PropNetMachineState pnstate = (PropNetMachineState) state;
		for (int i = 0; i < heuristics.length; i++) {
			if (pnstate.props[i]) heuristic += heuristics[i];
		}
		if (heuristic < MyPlayer.MIN_SCORE) heuristic = MyPlayer.MIN_SCORE;
		if (heuristic > MyPlayer.MAX_SCORE) heuristic = MyPlayer.MAX_SCORE;
		return heuristic;
	}

	private class Factor {
		public boolean[] factor;

		public Factor(Role role, List<Move> moves) {
			Set<Component> reachableBases = new HashSet<>();
			Map<GdlSentence, Proposition> propMap = smthread.m.p.getInputPropositions();
			for (Move move : moves) {
				if (move == null) continue;
				findComponentsForwards(propMap.get(ProverQueryBuilder.toDoes(role, move)),
						reachableBases);
			}
			List<Proposition> bases = smthread.m.props;
			factor = new boolean[bases.size()];
			for (int i = 0; i < bases.size(); i++) {
				factor[i] = reachableBases.contains(bases.get(i));
			}
		}

		@Override
		public int hashCode() {
			return Arrays.hashCode(factor);
		}

		@Override
		public boolean equals(Object other) {
			return Arrays.equals(factor, ((Factor) other).factor);
		}

		public double dist(Factor other) {
			int dist = 0;
			int tot = 0;
			for (int i = 0; i < factor.length; i++) {
				if (factor[i] != other.factor[i]) dist++;
				if (factor[i] || other.factor[i]) tot++;
			}
			return 1.0 * dist / tot;
		}
	}

	public void multiPlayerMetaGame(long timeout)
			throws MoveDefinitionException, TransitionDefinitionException {
		Role role = player.getRole();
		List<MetaGameDCThread> pool = new ArrayList<>();
		int n_thread = 4;
		Log.println("finding factors...");
		long start = System.currentTimeMillis();
		long alloc_factoring = start + (timeout - start) / 10;

		Map<Factor, Integer> factors = new HashMap<>();
		StateMachine machine = player.getStateMachine();
		MachineState initial = machine.getInitialState();
		while (System.currentTimeMillis() < alloc_factoring) {
			MachineState state = initial;
			while (!machine.isTerminal(state)) {
				List<Move> moves = getUsefulMoves(machine, role, state);
				if (moves.size() > 1) {
					Factor current = new Factor(role, moves);
					factors.put(current, factors.getOrDefault(current, 0) + 1);
				}
				state = machine.getRandomNextState(state);
			}
		}
		Factor max_factor = null;
		int max_size = -1;
		for (Factor f : factors.keySet()) {
			int count = factors.get(f);
			if (count > max_size) {
				max_factor = f;
				max_size = count;
			}
		}

		for (Factor f : factors.keySet()) {
			if (max_factor.dist(f) > 0.5 && factors.get(f) * 2 > max_size) {
				Log.println("found multiple distinct factors. abandoning piece heuristic.");
				return;
			}
		}
		Log.println("game has one factor. begin random exploration...");
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
		int ngame = 0;
		boolean[] canUseHeuristic = new boolean[heuristicCalcs.size()];
		for (int i = 0; i < heuristicCalcs.size(); i++) {
			double sum = 0;
			for (MetaGameDCThread thread : pool) {
				sum += thread.timeCalc[i].calculate().m;
			}
			Log.println(heuristicCalcs.get(i).term + " time correlation: " + sum / 4);
			canUseHeuristic[i] = sum < 0 && sum > -1;
		}
		for (MetaGameDCThread thread : pool) {
			for (MetaGameDCOut out : thread.output) {
				ngame++;
				for (int i = 0; i < heuristicCalcs.size(); i++) {
					if (!canUseHeuristic[i]) continue;
					heuristicCalcs.get(i).addData(out.counts[i], out.eval);
				}
			}
		}
		Log.println("games explored: " + ngame);
		computeHeuristic();
	}

	public boolean sameState(MachineState state1, MachineState state2) {
		if (propNetInitialized) {
			boolean[] props1 = ((PropNetMachineState) state1).props;
			boolean[] props2 = ((PropNetMachineState) state2).props;
			return Arrays.equals(props1, props2);
		}
		return state1.equals(state2);
	}

	public boolean contains(List<MachineState> states, MachineState target) {
		for (MachineState state : states) {
			if (sameState(state, target)) return true;
		}
		return false;
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
		gc();

		if (nextPossibles != null && !contains(nextPossibles, rootstate)) {
			nBehindServer++;
			long newclock = (timeout - System.currentTimeMillis()) / nBehindServer;
			Log.println("move transmission error. shortening play clock to " + newclock);
			timeout = System.currentTimeMillis() + newclock;
		} else nBehindServer = 1;

		if (checkStateMachineStatus()) {
			// reinit state machine
			machine = player.getStateMachine();
			rootstate = player.getCurrentState();
		}

		Move move = run_(machine, rootstate, role, moves, timeout);

		long start = System.currentTimeMillis();
		nextPossibles = new ArrayList<>();
		List<List<Move>> jmoves = machine.getLegalJointMoves(rootstate, role, move);
		for (List<Move> jmove : jmoves) {
			nextPossibles.add(machine.getNextState(rootstate, jmove));
		}
		Log.println("time to enumerate next states: " + (System.currentTimeMillis() - start));
		return move;
	}

	public void computeHeuristic() {
		int nbase = smthread.m.props.size();
		PriorityQueue<LinReg> linregs = new PriorityQueue<>();
		double tot_rsq = 0;
		heuristic_yint = 0;
		heuristics = new double[nbase];
		for (int i = 0; i < heuristicCalcs.size(); i++) {
			LinReg reg = heuristicCalcs.get(i).calculate();
			heuristicCalcs.get(i).clearData();
			linregs.add(reg);
			tot_rsq += reg.rsq;
			heuristic_yint += reg.rsq * reg.b;
			for (int j : heuristicProps.get(i)) {
				heuristics[j] += reg.rsq * reg.m;
			}
		}
		if (tot_rsq == 0) {
			Log.println("no piece heuristic");
			heuristic_yint = 50;
		} else {
			while (!linregs.isEmpty()) {
				LinReg reg = linregs.poll();
				Log.println(reg + " (m=" + (reg.rsq * reg.m / tot_rsq) + ")");
			}
			for (int i = 0; i < heuristics.length; i++) {
				heuristics[i] /= tot_rsq;
			}
			heuristic_yint /= tot_rsq;
			Log.printf("tot_rsq=%.3f, yint=%.3f\n", tot_rsq, heuristic_yint);
		}
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
		ignoreProps = null;
		if (propNetInitialized) {
			oldUseless = new HashMap<>();
			List<Proposition> bases = smthread.m.props;
			ignoreProps = new boolean[bases.size()];
			for (Role r : machine.findRoles()) {
				oldUseless.put(r, new HashSet<>(useless.get(r)));
			}
			Set<Component> reachableBases = new HashSet<>();
			Map<GdlSentence, Proposition> propMap = smthread.m.p.getInputPropositions();
			for (Move move : moves) {
				findComponentsForwards(propMap.get(ProverQueryBuilder.toDoes(role, move)),
						reachableBases);
			}

			reachableBases.retainAll(bases);
			Log.printf("%d of %d props relevant\n", reachableBases.size(), bases.size());
			int count = 0;
			Set<Component> ignore = new HashSet<>();
			for (Role r : machine.findRoles()) {
				for (Move action : machine.findActions(r)) {
					Component does = propMap.get(ProverQueryBuilder.toDoes(r, action));
					findComponentsForwards(does, ignore);
					if (!findAnyComponentForwards(does, new HashSet<>(), reachableBases)) {
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

		MTreeNode root = new MTreeNode(rootstate);
		expand(machine, role, root);

		DepthChargeThread[] threads = new DepthChargeThread[nthread];
		BlockingQueue<MTreeNode> input = new ArrayBlockingQueue<>(nthread);
		BlockingQueue<DCOut> output = new LinkedBlockingQueue<>();
		for (int i = 0; i < nthread; i++) {
			threads[i] = new DepthChargeThread(machines[i], role, timeout, input, output);
			threads[i].start();
		}
		FastThread ft = new FastThread(timeout, machines[nthread], role, rootstate);
		ft.start();
		int dctime = 0;
		while (System.currentTimeMillis() < timeout && !root.isProven()) {
			MTreeNode node = select(root);
			if (machine.isTerminal(node.state)) {
				backpropogate(node, findReward(machine, role, node.state), 0, true);
			} else {
				if (node.children.isEmpty()) {
					expand(machine, role, node);
				}
				try {
					long start = System.currentTimeMillis();
					input.put(node);
					dctime += System.currentTimeMillis() - start;
				} catch (InterruptedException e) {
					e.printStackTrace();
				}
				while (true) {
					DCOut out = output.poll();
					if (out == null) break;
					if (out.eval == FAIL) continue;
					backpropogate(out.node, out.eval, 0, false);
				}
			}
		}
		ft.kill = true;
		try {
			ft.join();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		MTreeNode bestChild = null;
		MTreeNode bestVisits = null;
		double bestVisitPct = Double.NEGATIVE_INFINITY;

		sanitizeMoves(role, root, moves);
		sanitizeMoves(role, ft.root, moves);

		for (MTreeNode child : root.children) {
			MTreeNode fastChild = ft.searchFor(child);
			double visitPct = Math.log(child.visits);
			if (fastChild != null) {
				child.lower = Math.max(child.lower, fastChild.lower);
				child.upper = Math.min(child.upper, fastChild.upper);
				visitPct += Math.log(fastChild.visits);
			}
			if (child.compareTo(bestChild) > 0) {
				bestChild = child;
			}
			if (bestVisits == null || visitPct > bestVisitPct) {
				bestVisitPct = visitPct;
				bestVisits = child;
			}

			Log.printf(
					"move=%s vp=%.3f v=(%d, %d) score=%.3f bound=(%.0f, %.0f) visits=%d depth=%d\n",
					child.move, visitPct, child.visits, (fastChild == null ? 0 : fastChild.visits),
					child.utility(), child.lower, child.upper, child.visits, child.depth);
		}
		if (bestVisits.utility() > bestChild.lower) bestChild = bestVisits;
		Log.printf("played=%s vp=%.3f visits=%d score=%.3f bound=(%.0f, %.0f) visits=%d depth=%d\n",
				bestChild.move, (bestChild == bestVisits ? bestVisitPct : 0), bestChild.visits,
				bestChild.utility(), bestChild.lower, bestChild.upper, root.visits, root.depth);
		Log.printf("time=%d dctime=%d\n", (System.currentTimeMillis() - timestart), dctime);
		Log.print("expected line: ");

		int cur_nmoves = root.children.size();
		int cur_nopp = 0;
		MTreeNode cur = bestChild;
		while (!cur.children.isEmpty()) {
			if (cur.jmove != null) {
				Log.printf(" %s (%d/%d)", cur.jmove, cur_nmoves, cur_nopp);
				cur_nmoves = cur.children.size();
			} else {
				cur_nopp = cur.children.size();
			}
			MTreeNode next = null;
			for (MTreeNode child : cur.children) {
				if (child.compareTo(next) > 0) next = child;
			}
			cur = next;
		}
		Log.println("");
		if (oldUseless != null) useless = oldUseless;
		return bestChild.move;
	}

	private void sanitizeMoves(Role role, MTreeNode root, Collection<Move> legal) {
		MTreeNode remove = null;
		for (MTreeNode child : root.children) {
			if (!legal.contains(child.move)) {
				Set<Move> uselessMoves = useless.get(role);
				uselessMoves.retainAll(legal);
				if (uselessMoves.size() > 0) child.move = uselessMoves.iterator().next();
				else remove = child;
			}
		}
		if (remove != null) root.children.remove(remove);
	}

	private double score(MTreeNode node, int sgn) {
		return node.score(sgn * CFACTOR);
	}

	private MTreeNode select(MTreeNode node) {
		while (true) {
			if (node.children.isEmpty()) return node;
			for (MTreeNode child : node.children) {
				if (child.visits == 0) return child;
			}
			MTreeNode best = null;
			if (node.isMaxNode()) {
				double score = Double.NEGATIVE_INFINITY;
				for (MTreeNode child : node.children) {
					if (child.isProven()) continue;
					double newscore = score(child, 1);
					if (newscore > score) {
						score = newscore;
						best = child;
					}
				}
			} else {
				double score = Double.POSITIVE_INFINITY;
				for (MTreeNode child : node.children) {
					if (child.isProven()) continue;
					double newscore = score(child, -1);
					if (newscore < score) {
						score = newscore;
						best = child;
					}
				}
			}
			node = best;
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
		if (uselessMove != null) {
			output.add(null);
		}
		return output;
	}

	// copied from StateMachine.java
	protected void crossProductMoves(List<List<Move>> legals, List<List<Move>> crossProduct,
			LinkedList<Move> partial) {
		if (partial.size() == legals.size()) {
			crossProduct.add(new ArrayList<Move>(partial));
		} else {
			for (Move move : legals.get(partial.size())) {
				partial.addLast(move);
				crossProductMoves(legals, crossProduct, partial);
				partial.removeLast();
			}
		}
	}

	public List<List<Move>> getUsefulJointMoves(StateMachine machine, MachineState state, Role role,
			Move move) throws MoveDefinitionException {
		List<List<Move>> legals = new ArrayList<List<Move>>();
		for (Role r : machine.getRoles()) {
			if (r.equals(role)) {
				List<Move> m = new ArrayList<Move>();
				m.add(move);
				legals.add(m);
			} else {
				legals.add(getUsefulMoves(machine, r, state));
			}
		}

		List<List<Move>> crossProduct = new ArrayList<List<Move>>();
		crossProductMoves(legals, crossProduct, new LinkedList<Move>());

		return crossProduct;
	}

	private void expand(StateMachine machine, Role role, MTreeNode node)
			throws MoveDefinitionException, TransitionDefinitionException {
		if (node.isMaxNode()) {
			for (Move move : getUsefulMoves(machine, role, node.state)) {
				MTreeNode newnode = new MTreeNode(node.state, move, node);
				node.children.add(newnode);
			}
		} else {
			for (List<Move> jmove : getUsefulJointMoves(machine, node.state, role, node.move)) {
				MachineState newstate = machine.findNext(jmove, node.state);
				if (propNetInitialized) {
					PropNetMachineState oldstate = (PropNetMachineState) node.state;
					PropNetMachineState newpstate = (PropNetMachineState) newstate;
					for (int i = 0; i < ignoreProps.length; i++) {
						if (ignoreProps[i]) newpstate.props[i] = oldstate.props[i];
					}
				}
				MTreeNode newnode = new MTreeNode(newstate, jmove, node);
				node.children.add(newnode);
			}
		}
	}

	private void backpropogate(MTreeNode node, double eval, int depth, boolean proven) {
		if (proven) {
			node.lower = node.upper = eval;
		}
		while (true) {
			node.visits++;
			node.sum_utility += eval;
			node.sum_sq += eval * eval;
			node.depth = Math.max(node.depth, depth);
			if (node.isMaxNode()) depth++;
			node = node.parent;
			if (node == null) return;
			if (proven) proven = node.setBounds();
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
		return;
	}

	private class DepthChargeThread extends Thread {

		private StateMachine machine;
		private Role role;
		private long timeout;
		private BlockingQueue<MTreeNode> input;
		private BlockingQueue<DCOut> output;

		public DepthChargeThread(StateMachine machine, Role role, long timeout,
				BlockingQueue<MTreeNode> input, BlockingQueue<DCOut> output) {
			this.machine = machine;
			this.role = role;
			this.timeout = timeout;
			this.input = input;
			this.output = output;
		}

		private DCOut simulate(MTreeNode node) throws MoveDefinitionException,
				TransitionDefinitionException, GoalDefinitionException {
			MachineState state = node.state;
			if (node.move != null) state = machine.getRandomNextState(state, role, node.move);
			double score;
			if (propNetInitialized) {
				JustKiddingPropNetStateMachine pnsm = (JustKiddingPropNetStateMachine) machine;
				score = findReward(pnsm.internalDC((PropNetMachineState) state));
			} else {
				while (!machine.isTerminal(state)) {
					if (System.currentTimeMillis() > timeout) return new DCOut(node, FAIL);
					state = machine.getRandomNextState(state);
				}
				score = findReward(machine, role, state);
			}
			return new DCOut(node, score);
		}

		@Override
		public void run() {
			while (true) {
				try {
					MTreeNode node = input.poll(
							timeout - System.currentTimeMillis() + MyPlayer.TIMEOUT_BUFFER,
							TimeUnit.MILLISECONDS);
					if (node == null) return;
					output.offer(simulate(node));
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		}
	}

	private static class MTreeNode implements Comparable<MTreeNode> {
		// prior: sum squares = 10000 so that stdev != 0
		public int visits = 0;
		public double sum_utility = 0;
		public double sum_sq = 10000;
		// bounds
		public double lower = MyPlayer.MIN_SCORE;
		public double upper = MyPlayer.MAX_SCORE;

		public List<MTreeNode> children = new ArrayList<>();
		public MTreeNode parent;

		public MachineState state;
		public Move move; // null if max-node; non-null if min-node
		public List<Move> jmove;
		public int depth = 0;
		public boolean isMaxNode;

		public MTreeNode(MachineState state) {
			this.state = state;
			isMaxNode = true;
		}

		public MTreeNode(MachineState state, List<Move> jmove, MTreeNode parent) {
			this.parent = parent;
			this.jmove = jmove;
			this.state = state;
			isMaxNode = true;
		}

		public MTreeNode(MachineState state, Move move, MTreeNode parent) {
			this.parent = parent;
			this.move = move;
			this.state = state;
			isMaxNode = false;
		}

		public int compareTo(MTreeNode other) {
			if (other == null) return 1;
			int cmp = Double.compare(utility(), other.utility());
			if (cmp != 0) return cmp;
			cmp = Double.compare(lower, other.lower);
			if (cmp != 0) return cmp;
			cmp = Double.compare(upper, other.upper);
			return Double.compare(visits, other.visits);
		}

		public boolean setBounds() {
			double oldupp = upper, oldlow = lower;
			if (isMaxNode()) {
				upper = MyPlayer.MIN_SCORE;
				lower = MyPlayer.MIN_SCORE;
				for (MTreeNode c : children) {
					upper = Math.max(upper, c.upper);
					lower = Math.max(lower, c.lower);
				}
			} else {
				upper = MyPlayer.MAX_SCORE;
				lower = MyPlayer.MAX_SCORE;
				for (MTreeNode c : children) {
					upper = Math.min(upper, c.upper);
					lower = Math.min(lower, c.lower);
				}
			}
			return upper != oldupp || lower != oldlow;
		}

		public double putInBounds(double eval) {
			if (eval < lower) eval = lower;
			if (eval > upper) eval = upper;
			return eval;
		}

		public boolean isProven() {
			return lower == upper;
		}

		public boolean isMaxNode() {
			return isMaxNode;
		}

		public double utility() {
			if (visits == 0) return putInBounds(1);
			return putInBounds(sum_utility / visits);
		}

		// dynamic score: multiplies by standard deviation
		public double score(double c) {
			double util = sum_utility / visits;
			double var = sum_sq / visits - util * util;
			return util + c * Math.sqrt(Math.log(parent.visits) / visits * var);
		}
	}

	private static class DCOut {
		double eval;
		MTreeNode node;

		public DCOut(MTreeNode node, double eval) {
			this.eval = eval;
			this.node = node;
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

	private boolean findAnyComponentForwards(Component current, Set<Component> visited,
			Set<Component> target) {
		if (current == null) return false;
		if (target.contains(current)) return true;
		if (visited.contains(current)) return false;
		visited.add(current);

		for (Component next : current.getOutputs()) {
			if (findAnyComponentForwards(next, visited, target)) return true;
		}
		return false;
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

		private int howUseful(Role role, Move move) {
			Set<Component> out = new HashSet<>();
			findComponentsForwards(
					m.p.getInputPropositions().get(ProverQueryBuilder.toDoes(role, move)), out);
			return out.size();
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
					if (!noops.containsKey(role)
							|| howUseful(role, noops.get(role)) > howUseful(role, move))
						noops.put(role, move);
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

			heuristicMap = new HashMap<>();
			heuristicProps = new ArrayList<>();
			heuristicCalcs = new ArrayList<>();
			// find heurisitics
			for (int i = 0; i < m.props.size(); i++) {
				GdlSentence base = m.props.get(i).getName().get(0).toSentence();
				if (base.arity() < 3) continue;
				GdlTerm term = base.get(base.arity() - 1);
				if (!heuristicMap.containsKey(term)) {
					heuristicMap.put(term, heuristicProps.size());
					heuristicCalcs.add(new LinRegCalc(term));
					heuristicProps.add(new ArrayList<>());
				}
				heuristicProps.get(heuristicMap.get(term)).add(i);

			}

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

	// FastThread does not do depth charges, ergo it is deterministic.
	private class FastThread extends Thread {
		private long timeout;
		private StateMachine machine;
		private Role role;
		private MachineState rootstate;

		public MTreeNode root;
		public boolean kill;

		public FastThread(long timeout, StateMachine machine, Role role, MachineState rootstate) {
			this.timeout = timeout;
			this.machine = machine;
			this.role = role;
			this.rootstate = rootstate;
		}

		public MTreeNode searchFor(MTreeNode node) {
			for (MTreeNode child : root.children) {
				if (child.move.equals(node.move)) return child;
			}
			return null;
		}

		public void run_() throws MoveDefinitionException, TransitionDefinitionException,
				GoalDefinitionException {
			root = new MTreeNode(rootstate);
			expand(machine, role, root);
			while (System.currentTimeMillis() < timeout && !kill) {
				if (root.isProven()) break;
				MTreeNode node = select(root);
				expand(machine, role, node);
				if (machine.isTerminal(node.state)) {
					backpropogate(node, findReward(machine, role, node.state), 0, true);
				} else {
					backpropogate(node, heuristic(node.state), 0, false);
				}
			}
			Log.printf("fastresult: bound=(%.0f, %.0f) visits=%d depth=%d\n", root.lower,
					root.upper, root.visits, root.depth);
		}

		@Override
		public void run() {
			try {
				run_();
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
	}

	private static class LinReg implements Comparable<LinReg> {
		public double m;
		public double b;
		public double rsq;
		public GdlTerm term;

		public LinReg(GdlTerm term) {
			this.term = term;
		}

		public int compareTo(LinReg other) {
			return -Double.compare(rsq, other.rsq);
		}

		@Override
		public String toString() {
			return String.format("%s: y = %.3fx + %.3f (r^2=%.3f)", term, m, b, rsq);
		}
	}

	private static class LinRegCalc {
		private double sx = 0;
		private double sx2 = 0;
		private double sy = 0;
		private double sxy = 0;
		private double sy2 = 0;
		private int n = 0;
		private GdlTerm term;

		public LinRegCalc(GdlTerm term) {
			this.term = term;
		}

		public void clearData() {
			sx = sy = sxy = sx2 = sy2 = n = 0;
		}

		public void addData(double x, double y) {
			sx += x;
			sy += y;
			sxy += x * y;
			sx2 += x * x;
			sy2 += y * y;
			n++;
		}

		public LinReg calculate() {
			LinReg linreg = new LinReg(term);
			linreg.m = (n * sxy - sx * sy) / (n * sx2 - sx * sx);
			linreg.b = (sy - linreg.m * sx) / n;
			double rnum = n * sxy - sx * sy;
			linreg.rsq = (rnum * rnum) / ((n * sx2 - sx * sx) * (n * sy2 - sy * sy));
			if (!Double.isFinite(linreg.b) || !Double.isFinite(linreg.rsq)) {
				linreg.m = linreg.b = linreg.rsq = 0; // NaN --> no correlation...
			}
			return linreg;
		}
	}
}