import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Set;
import java.util.Stack;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.TimeUnit;

import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.gdl.grammar.Gdl;
import org.ggp.base.util.gdl.grammar.GdlConstant;
import org.ggp.base.util.gdl.grammar.GdlSentence;
import org.ggp.base.util.propnet.architecture.Component;
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
	private static final double CFACTOR = 1.0;
	private StateMachine[] machines;
	private boolean propNetInitialized = false;
	private MyPlayer gamer;

	private StateMachineCreatorThread smthread;

	// communication between metagame threads
	private Stack<Move> solution;
	private Map<Role, Set<Move>> useless;
	private Set<Component> reachableBases;
	private Map<Proposition, Proposition> legalToInputMap;
	private int nUsefulRoles;

	private boolean checkStateMachineStatus() {
		if (!propNetInitialized && !smthread.isAlive()) {
			gamer.switchToNewPropnets(smthread.m, machines);
			Log.println("propnets initialized");
			return propNetInitialized = true;
		}
		return false;
	}

	public Experiment(MyPlayer gamer, List<Gdl> description) {
		this.gamer = gamer;
		machines = new StateMachine[MyPlayer.N_THREADS];
		for (int i = 0; i < MyPlayer.N_THREADS; i++) {
			machines[i] = gamer.getStateMachine();
			machines[i].initialize(description);
		}
		smthread = new StateMachineCreatorThread(gamer.getRole(), description);
		smthread.start();
	}

	@Override
	public void metaGame(StateMachineGamer gamer, long timeout) {
		useless = new HashMap<>();
		solution = null;

		Set<GdlConstant> all = new HashSet<>();
		Set<GdlConstant> impossibles = new HashSet<>();

		StateMachine machine = gamer.getStateMachine();
		for (Role role : machine.findRoles()) {
			useless.put(role, new HashSet<>());
		}

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

		if (nUsefulRoles != 1) return;
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

		int nignored = 0;
		for (int i = 0; i < bases.size(); i++) {
			if (!smthread.reachable.contains(bases.get(i))) {
				ignoreProps[i] = true;
				nignored++;
			}
		}

		Log.println("ignoring " + nignored + " additional irrelevant props");

		AStar alg = new AStar(ignoreProps);
		long start = System.currentTimeMillis();
		try {
			solution = alg.run(timeout);
		} catch (Exception e) {
			e.printStackTrace();
		}
		if (solution != null) {
			Log.println("solution found in " + (System.currentTimeMillis() - start) + " ms");
		} else {
			Log.println("solver failed to find solution");
		}
	}

	public boolean sameState(MachineState state1, MachineState state2) {
		if (propNetInitialized) {
			boolean[] props1 = ((PropNetMachineState) state1).props;
			boolean[] props2 = ((PropNetMachineState) state2).props;
			return Arrays.equals(props1, props2);
		}
		return state1.equals(state2);
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
		// we don't cache anyway. might as well...
		if (moves.size() == 1) {
			Log.println("one legal move: " + moves.get(0));
			return moves.get(0);
		}
		Log.println("threads running: " + Thread.activeCount());
		if (checkStateMachineStatus()) {
			// reinit state machine
			machine = gamer.getStateMachine();
			rootstate = gamer.getCurrentState();
		}
		reachableBases = null;
		if (propNetInitialized) {
			reachableBases = new HashSet<>();
			Map<GdlSentence, Proposition> propMap = smthread.m.p.getInputPropositions();
			for (Move move : moves) {
				findComponentsForwards(propMap.get(ProverQueryBuilder.toDoes(role, move)),
						reachableBases);
			}
			reachableBases.retainAll(smthread.m.props);
			Log.printf("%d of %d props relevant\n", reachableBases.size(), smthread.m.props.size());
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
		BlockingQueue<DCOut> output = new ArrayBlockingQueue<>(nthread);
		for (int i = 0; i < nthread; i++) {
			threads[i] = new DepthChargeThread(machines[i], role, timeout, input, output);
			threads[i].start();
		}
		FastThread ft = new FastThread(timeout, machines[nthread], role, rootstate);
		ft.start();
		while (System.currentTimeMillis() < timeout && !root.isProven()) {
			MTreeNode node = select(root);
			if (machine.isTerminal(node.state)) {
				backpropogate(node, machine.findReward(role, node.state), 0, true);
			} else {
				if (node.children.isEmpty()) expand(machine, role, node);
				input.offer(node);
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
		sanitizeMoves(role, root, moves);
		sanitizeMoves(role, ft.root, moves);
		for (MTreeNode child : root.children) {
			MTreeNode fastChild = ft.searchFor(child);
			if (fastChild != null) {
				child.lower = Math.max(child.lower, fastChild.lower);
				child.upper = Math.min(child.upper, fastChild.upper);
			}
			if (bestChild == null || child.utility() > bestChild.utility()
					|| (child.utility() == bestChild.utility() && child.visits > bestChild.visits))
				bestChild = child;
			Log.println("move=" + info(child, child));
		}
		Log.println("played=" + info(bestChild, root));
		Log.println("tot time = " + (System.currentTimeMillis() - timestart));
		Log.print("expected line: ");
		while (!root.children.isEmpty()) {
			MTreeNode next = null;
			for (MTreeNode child : root.children) {
				if (next == null || child.depth > next.depth) next = child;
			}
			root = next;
			if (root.jmove != null) Log.print(" " + root.jmove);
		}
		Log.println("");
		return bestChild.move;
	}

	private void sanitizeMoves(Role role, MTreeNode root, Collection<Move> legal) {
		for (MTreeNode child : root.children) {
			if (child.move == null) {
				Set<Move> uselessMoves = useless.get(role);
				uselessMoves.retainAll(legal);
				if (uselessMoves.size() > 0) child.move = uselessMoves.iterator().next();
				else continue;
			}
		}
	}

	private double score(MTreeNode node, int sgn) {
		return node.score(sgn * CFACTOR);
	}

	private String info(MTreeNode scoreNode, MTreeNode rootNode) {
		return String.format("%s score=%f ci=(%f, %f) bound=(%.0f, %.0f) visits=%d depth=%d",
				scoreNode.move, scoreNode.utility(), score(scoreNode, -1), score(scoreNode, 1),
				scoreNode.lower, scoreNode.upper, rootNode.visits, rootNode.depth);
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

	private boolean hasNoEffect(Role role, Move move) {
		if (!propNetInitialized) return false;
		return !findAnyComponentForwards(
				smthread.m.p.getInputPropositions().get(ProverQueryBuilder.toDoes(role, move)),
				new HashSet<>(), reachableBases);
	}

	private List<Move> getUsefulMoves(StateMachine machine, Role role, MachineState state) {
		List<Move> actions = null;
		try {
			actions = machine.findLegals(role, state);
		} catch (MoveDefinitionException e) {
			e.printStackTrace();
		}
		if (!propNetInitialized) return actions;
		Set<Move> uselessMoves = useless.get(role);

		List<Move> output = new ArrayList<>();
		boolean hasUseless = false;
		for (Move move : actions) {
			if (uselessMoves.contains(move) || hasNoEffect(role, move)) {
				hasUseless = true;
				continue;
			}
			output.add(move);
		}
		if (hasUseless) {
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
		return;
	}

	private static class DepthChargeThread extends Thread {
		public static final int MAX_SCORE = 99;
		public static final int MIN_SCORE = 1;

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
			while (!machine.isTerminal(state)) {
				if (System.currentTimeMillis() > timeout) return new DCOut(node, MCTS.FAIL);
				state = machine.getRandomNextState(state);
			}
			double score = machine.findReward(role, state);
			if (score < MIN_SCORE) score = MIN_SCORE;
			if (score > MAX_SCORE) score = MAX_SCORE;
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

	private static class MTreeNode {
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
		if (visited.contains(current)) return;
		visited.add(current);
		for (Component parent : current.getInputs()) {
			findComponentsBackwards(parent, visited);
		}
	}

	private boolean findAnyComponentForwards(Component current, Set<Component> visited,
			Set<Component> target) {
		if (target.contains(current)) return true;
		if (visited.contains(current)) return false;
		visited.add(current);
		// if (legalToInputMap.containsKey(current)) current = legalToInputMap.get(current);
		for (Component next : current.getOutputs()) {
			if (findAnyComponentForwards(next, visited, target)) return true;
		}
		return false;
	}

	private void findComponentsForwards(Component current, Set<Component> visited) {
		if (visited.contains(current)) return;
		visited.add(current);
		if (legalToInputMap.containsKey(current)) current = legalToInputMap.get(current);
		for (Component next : current.getOutputs()) {
			findComponentsForwards(next, visited);
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
			Log.println("pruning irrelevant inputs");
			reachable = new HashSet<>();
			findComponentsBackwards(m.p.getTerminalProposition(), reachable);
			Set<Component> goals = new HashSet<>();
			goals.addAll(m.p.getGoalPropositions().get(role));
			Map<GdlSentence, Proposition> inputs = m.p.getInputPropositions();
			Collection<Proposition> values = inputs.values();
			legalToInputMap = new HashMap<>(smthread.m.p.getLegalInputMap());
			for (Proposition value : values) {
				legalToInputMap.remove(value);
			}
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
			Log.println("propnet ready");
		}
	}

	// a namespace for astar-related methods...or really just a DFS
	private class AStar {
		boolean[] ignoreProps;

		public AStar(boolean[] ignoreProps) {
			this.ignoreProps = ignoreProps;
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

		// psuedocode from Wikipedia on A*
		public Stack<Move> run(long timeout) throws GoalDefinitionException,
				MoveDefinitionException, TransitionDefinitionException {
			StateMachine machine = gamer.getStateMachine();
			Role role = gamer.getRole();
			MachineState initial = machine.getInitialState();
			Set<MachineState> closed = new TreeSet<>(this::compare);
			Map<MachineState, StateInfo> info = new TreeMap<>(this::compare);

			PriorityQueue<PQEntry> pq = new PriorityQueue<>();
			pq.add(new PQEntry(initial, 0));
			info.put(initial, new StateInfo(null, null, 0));
			int best_reward = 0;
			Stack<Move> best = null;

			while (!pq.isEmpty()) {
				if (System.currentTimeMillis() > timeout) return null;
				MachineState u = pq.poll().state;
				if (closed.contains(u)) continue;
				closed.add(u);
				if (machine.isTerminal(u)) {
					int reward = machine.findReward(role, u);
					if (reward > best_reward) {
						best = reconstruct(info, u);
						best_reward = reward;
						if (best_reward == MyPlayer.MAX_SCORE) return best;
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
			Log.println("best solution has value " + best_reward);
			return best;
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
					backpropogate(node, machine.findReward(role, node.state), 0, true);
				} else {
					backpropogate(node, 50, 0, false);
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
}