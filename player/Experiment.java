import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Set;
import java.util.Stack;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;

import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.gdl.grammar.Gdl;
import org.ggp.base.util.gdl.grammar.GdlConstant;
import org.ggp.base.util.gdl.grammar.GdlSentence;
import org.ggp.base.util.propnet.architecture.Component;
import org.ggp.base.util.propnet.architecture.components.Proposition;
import org.ggp.base.util.propnet.architecture.components.Transition;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;

public class Experiment extends Method {

	public static final int FAIL = MyPlayer.MIN_SCORE - 1;
	private static final double CFACTOR = 1.0;
	private List<MTreeNode> cache = new ArrayList<>();
	private List<MTreeNode> fastCache = new ArrayList<>();
	private StateMachine[] machines;
	private boolean propNetInitialized = false;
	private MyPlayer gamer;
	private GdlConstant clockConstant;
	private Set<Integer> ignoreProps = new HashSet<Integer>();
	private StateMachineCreatorThread smthread;
	private Set<Integer> targetSet;
	private Stack<Move> solution;

	// if the metapropnetstatemachinefactory has finished, update the machines
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
		smthread = new StateMachineCreatorThread(description);
		smthread.start();
	}

	@Override
	public void metaGame(StateMachineGamer gamer, long timeout) {
		clockConstant = null;
		solution = null;

		Set<GdlConstant> all = new HashSet<>();
		Set<GdlConstant> impossibles = new HashSet<>();

		StateMachine machine = gamer.getStateMachine();

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

		all.removeAll(impossibles);
		if (all.size() == 0) Log.println("no clock");
		else if (all.size() > 1) Log.println("too many possible clocks: " + all);
		else Log.println("the clock is " + (clockConstant = all.iterator().next()));

		if (!checkStateMachineStatus()) {
			Log.println("Still building propnet...");
			return;
		}

		machine = gamer.getStateMachine();

		if (machine.getRoles().size() > 1) return;
		if (clockConstant != null) {
			Log.println("ignoring clock proposition " + clockConstant);
			Map<GdlSentence, Integer> basemap = new HashMap<>();
			for (int i = 0; i < smthread.m.props.size(); i++) {
				basemap.put(smthread.m.props.get(i).getName(), i);
			}
			for (GdlSentence g : basemap.keySet()) {
				if (g.get(0).toSentence().getName().equals(clockConstant)) {
					int idx = basemap.get(g);
					ignoreProps.add(idx);
					targetSet.remove(idx);
				}
			}
		}
		Log.println("single player game: " + targetSet.size() + " target propositions");
		AStar alg = new AStar();
		try {
			solution = alg.run(timeout);
		} catch (Exception e) {
			e.printStackTrace();
		}
		if (solution != null) Log.println("solution found!");
	}

	private boolean sameState(MachineState state1, MachineState state2) {
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
		Log.println("--------------------");
		if (solution != null && !solution.isEmpty()) {
			Move move = solution.pop();
			Log.println("solution move: " + move);
			if (machine.getLegalMoves(rootstate, role).contains(move)) return move;
		}

		if (checkStateMachineStatus()) {
			// reinit state machine
			machine = gamer.getStateMachine();
			rootstate = gamer.getCurrentState();
			cache.clear();
			fastCache.clear();
		}

		long timestart = System.currentTimeMillis();

		int nthread = MyPlayer.N_THREADS - 1;
		if (!propNetInitialized) nthread--;
		Log.println("depth charge threads: " + nthread);

		// set up tree
		MTreeNode root = null;
		for (MTreeNode node : cache) {
			if (sameState(node.state, rootstate)) {
				Log.printf("cache retrieval: nodes=%d depth=%d\n", node.visits, node.depth);
				root = node;
				break;
			}
		}
		cache.clear();
		if (root == null) {
			root = new MTreeNode(rootstate, null, null);
			expand(machine, role, root);
		}
		root.parent = null;
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
		for (MTreeNode child : bestChild.children) {
			cache.add(child);
		}
		Log.println("played=" + info(bestChild, root));
		Log.println("tot time = " + (System.currentTimeMillis() - timestart));
		for (int i = 0; i < nthread; i++) {
			threads[i].input.offer(DepthChargeThread.HALT);
		}
		return bestChild.move;
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

	private void expand(StateMachine machine, Role role, MTreeNode node)
			throws MoveDefinitionException, TransitionDefinitionException {
		if (node.isMaxNode()) { // max-node
			List<Move> actions = machine.findLegals(role, node.state);
			for (Move move : actions) {
				MTreeNode newnode = new MTreeNode(node.state, move, node);
				node.children.add(newnode);
			}
		} else {
			List<List<Move>> actions = machine.getLegalJointMoves(node.state, role, node.move);
			for (List<Move> jmove : actions) {
				MachineState newstate = machine.findNext(jmove, node.state);
				MTreeNode newnode = new MTreeNode(newstate, null, node);
				node.children.add(newnode);
			}
		}
		Collections.shuffle(node.children);
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
		public static final MTreeNode HALT = new MTreeNode(null, null, null);
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
					MTreeNode node = input.take();
					if (node == HALT) return;
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
		public int depth = 0;

		public MTreeNode(MachineState state, Move move, MTreeNode parent) {
			this.parent = parent;
			this.move = move;
			this.state = state;
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
			return move == null;
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

	private class StateMachineCreatorThread extends Thread {
		private List<Gdl> description;
		public JustKiddingPropNetStateMachine m;

		public StateMachineCreatorThread(List<Gdl> description) {
			this.description = description;
		}

		public void findBases(Component current, Set<Component> visited) {
			if (current instanceof Transition) return;
			if (visited.contains(current)) return;
			visited.add(current);
			for (Component parent : current.getInputs()) {
				findBases(parent, visited);
			}
		}

		@Override
		public void run() {
			m = new JustKiddingPropNetStateMachine();
			m.initialize(description);
			Log.println("computing goal similarity heuristic...");
			Set<Proposition> goalProps = m.p.getGoalPropositions().get(gamer.getRole());
			Set<GdlSentence> bases = m.p.getBasePropositions().keySet();
			Set<Proposition> totals = new HashSet<>();
			targetSet = new HashSet<>();
			for (Proposition goal : goalProps) {
				int val = Integer.parseInt(goal.getName().get(1).toString());
				if (val != MyPlayer.MAX_SCORE) continue;
				Set<Component> result = new HashSet<>();
				findBases(goal, result);
				for (Component c : result) {
					if (!(c instanceof Proposition)) continue;
					Proposition sent = (Proposition) c;
					if (bases.contains(sent.getName())) totals.add(sent);
				}
			}
			for (int i = 0; i < m.props.size(); i++) {
				Proposition base = m.props.get(i);
				if (totals.contains(base)) targetSet.add(i);
			}
			Log.println("propnet ready");
		}
	}

	// a namespace for astar-related methods.
	private class AStar {
		private int compare(MachineState state1, MachineState state2) {
			boolean[] props1 = ((PropNetMachineState) state1).props;
			boolean[] props2 = ((PropNetMachineState) state2).props;
			for (int i = 0; i < props1.length; i++) {
				if (props1[i] == props2[i] || ignoreProps.contains(i)) continue;
				return props1[i] ? 1 : -1;
			}
			return 0;
		}

		private int heuristic(MachineState state) {
			boolean[] props = ((PropNetMachineState) state).props;
			int distance = 0;
			for (int i : targetSet) {
				if (!props[i]) distance++;
			}
			return distance;
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
			pq.add(new PQEntry(initial, heuristic(initial)));
			info.put(initial, new StateInfo(null, null, 0));

			while (!pq.isEmpty()) {
				if (System.currentTimeMillis() > timeout) return null;
				MachineState u = pq.poll().state;
				if (closed.contains(u)) continue;
				closed.add(u);
				if (machine.isTerminal(u) && machine.findReward(role, u) == MyPlayer.MAX_SCORE) {
					return reconstruct(info, u);
				}
				int newDist = info.get(u).distance + 1;
				for (Move move : machine.getLegalMoves(u, role)) {
					MachineState v = machine.getNextState(u, Arrays.asList(new Move[] { move }));
					StateInfo vinfo = info.get(v);
					if (vinfo == null) {
						info.put(v, new StateInfo(u, move, newDist));
						pq.add(new PQEntry(v, newDist + heuristic(v)));
					} else if (!closed.contains(u) && vinfo.distance > newDist) {
						vinfo.distance = newDist;
						vinfo.parent = u;
						vinfo.parentMove = move;
						pq.add(new PQEntry(v, newDist + heuristic(v)));
					}
				}
			}
			return null; // failure
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
			root = null;
			for (MTreeNode node : fastCache) {
				if (sameState(node.state, rootstate)) {
					Log.printf("fast cache: nodes=%d depth=%d\n", node.visits, node.depth);
					root = node;
					break;
				}
			}
			fastCache.clear();
			if (root == null) {
				root = new MTreeNode(rootstate, null, null);
				expand(machine, role, root);
			}
			root.parent = null;
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
			for (MTreeNode child : root.children) {
				for (MTreeNode next : child.children) {
					fastCache.add(next);
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