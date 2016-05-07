import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.LinkedBlockingQueue;

import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.gdl.grammar.Gdl;
import org.ggp.base.util.gdl.grammar.GdlConstant;
import org.ggp.base.util.gdl.grammar.GdlSentence;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;

public class MCTS extends Method {

	public static final int FAIL = MyPlayer.MIN_SCORE - 1;
	private static final double CFACTOR = 2.0;
	private List<MTreeNode> cache = new ArrayList<>();
	private StateMachine[] machines;
	private boolean propNetInitialized = false;
	private MyPlayer gamer;
	private GdlConstant clockConstant;
	private Set<Integer> ignoreProps = new HashSet<Integer>();
	private Map<MachineState, MTreeNode> pnCache = new TreeMap<>(this::compare);

	private StateMachineCreatorThread smthread;

	/* BEGIN MACHINESTATE HELPER METHODS */

	private int compare(MachineState state1, MachineState state2) {
		boolean[] props1 = ((PropNetMachineState) state1).props;
		boolean[] props2 = ((PropNetMachineState) state2).props;
		for (int i = 0; i < props1.length; i++) {
			if (props1[i] == props2[i] || ignoreProps.contains(i)) continue;
			return props1[i] ? 1 : -1;
		}
		return 0;
	}

	public boolean contains(Collection<MachineState> collection, MachineState test) {
		for (MachineState s : collection) {
			if (sameState(s, test)) return true;
		}
		return false;
	}

	private boolean sameState(MachineState state1, MachineState state2) {
		if (propNetInitialized) {
			boolean[] props1 = ((PropNetMachineState) state1).props;
			boolean[] props2 = ((PropNetMachineState) state2).props;
			for (int i = 0; i < props1.length; i++) {
				if (ignoreProps.contains(i)) continue;
				if (props1[i] != props2[i]) return false;
			}
			return true;
		}
		return state1.equals(state2);
	}

	private class StateMachineCreatorThread extends Thread {
		private List<Gdl> description;
		public BetterMetaPropNetStateMachineFactory m;

		public StateMachineCreatorThread(List<Gdl> description) {
			this.description = description;
		}

		@Override
		public void run() {
			m = new BetterMetaPropNetStateMachineFactory(description);
			Log.println("Propnets ready");
		}
	}

	// if the metapropnetstatemachinefactory has finished, update the machines
	private boolean checkStateMachineStatus() {
		if (propNetInitialized || smthread.isAlive()) return false;
		gamer.switchToPropnets(smthread.m, machines);
		Log.println("Propnets initialized");
		propNetInitialized = true;
		if (clockConstant != null) {
			Log.println("Ignoring clock proposition " + clockConstant);
			Map<GdlSentence, Integer> basemap = new HashMap<>();
			for (int i = 0; i < smthread.m.bases.size(); i++) {
				basemap.put(smthread.m.bases.get(i).getName(), i);
			}
			for (GdlSentence g : basemap.keySet()) {
				if (g.get(0).toSentence().getName().equals(clockConstant)) {
					ignoreProps.add(basemap.get(g));
				}
			}
		}
		return true;
	}

	public MCTS(MyPlayer gamer, List<Gdl> description) {
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
		pnCache.clear();
		StateMachine machine = gamer.getStateMachine();
		MachineState state = machine.getInitialState();
		Set<GdlConstant> all = new HashSet<>();
		Set<GdlConstant> impossibles = new HashSet<>();

		while (System.currentTimeMillis() < timeout && smthread.isAlive()) {
			Map<GdlConstant, Set<GdlSentence>> possibles = new HashMap<>();
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

		clockConstant = null;
		all.removeAll(impossibles);
		if (all.size() == 0) Log.println("no clock");
		else if (all.size() > 1) Log.println("too many possible clocks: " + all);
		else Log.println("the clock is " + (clockConstant = all.iterator().next()));

		if (!checkStateMachineStatus()) {
			Log.println("Still building propnet...");
			return;
		}
	}

	@Override
	public Move run(StateMachine machine, MachineState rootstate, Role role, List<Move> moves,
			long timeout) throws GoalDefinitionException, MoveDefinitionException,
					TransitionDefinitionException {
		if (checkStateMachineStatus()) {
			// reinit state machine
			machine = gamer.getStateMachine();
			rootstate = gamer.getCurrentState();
			cache.clear();
		}
		long timestart = System.currentTimeMillis();
		long simtime = 0;

		Log.println("--------------------");
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
		if (root == null || root.children.isEmpty()) { // second case for repeated nodes
			root = new MTreeNode(rootstate, null);
			expand(machine, role, root);
		}
		// root.parents.clear();
		HSimThread[] threads = new HSimThread[MyPlayer.N_THREADS];
		BlockingQueue<MTreeNode> input = new LinkedBlockingQueue<>();
		BlockingQueue<Integer> output = new LinkedBlockingQueue<>();
		for (int i = 0; i < MyPlayer.N_THREADS; i++) {
			threads[i] = new HSimThread(machines[i], role, timeout, input, output);
			threads[i].start();
		}
		while (System.currentTimeMillis() < timeout) {
			if (root.isProven()) {
				Log.println("Game solved with value " + root.lower);
				break;
			}
			MTreeNode node = select(root);
			if (machine.isTerminal(node.state)) {
				backpropogate(node, machine.findReward(role, node.state), true);
			} else {
				expand(machine, role, node);
				long start = System.currentTimeMillis();
				for (int i = 0; i < MyPlayer.N_THREADS; i++) {
					input.offer(node);
				}
				for (int i = 0; i < MyPlayer.N_THREADS; i++) {
					try {
						int eval = output.take();
						if (eval == FAIL) continue;
						backpropogate(node, eval, false);
					} catch (InterruptedException e) {
						e.printStackTrace();
					}
				}
				simtime += System.currentTimeMillis() - start;
			}
		}
		MTreeNode bestChild = null;
		for (MTreeNode child : root.children) {
			if (bestChild == null || child.utility() > bestChild.utility()) bestChild = child;
			Log.println("move=" + info(child, child));
		}
		for (MTreeNode child : bestChild.children) {
			cache.add(child);
		}
		Log.println("played=" + info(bestChild, root));
		Log.println("tot time = " + (System.currentTimeMillis() - timestart));
		Log.println("sim time = " + simtime);
		for (int i = 0; i < MyPlayer.N_THREADS; i++) {
			threads[i].input.offer(HSimThread.HALT);
		}
		return bestChild.move;
	}

	private double score(MTreeNode node, int sgn) {
		return node.score(sgn * CFACTOR);
	}

	private String info(MTreeNode scoreNode, MTreeNode rootNode) {
		return String.format("%s score=%f ci=(%f, %f) bound=(%d, %d) visits=%d depth=%d",
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

	// returns whether node is a parent of child
	private boolean isAncestor(MTreeNode node, MTreeNode child) {
		if (node == child) return true;
		for (MTreeNode parent : child.parents) {
			if (isAncestor(node, parent)) return true;
		}
		return false;
	}

	private void expand(StateMachine machine, Role role, MTreeNode node)
			throws MoveDefinitionException, TransitionDefinitionException {
		if (node.isMaxNode()) { // max-node
			List<Move> actions = machine.findLegals(role, node.state);
			for (Move move : actions) {
				MTreeNode newnode = new MTreeNode(node.state, move);
				newnode.parents.add(node);
				node.children.add(newnode);
			}
		} else {
			List<List<Move>> actions = machine.getLegalJointMoves(node.state, role, node.move);
			for (List<Move> jmove : actions) {
				MachineState newstate = machine.findNext(jmove, node.state);
				MTreeNode newnode = new MTreeNode(newstate, null);
				newnode.parents.add(node);
				node.children.add(newnode);
			}
		}
		Collections.shuffle(node.children);
	}

	private static final int MIN_EVAL = 1;
	private static final int MAX_EVAL = 99; // never propogate 0 or 100

	private void backpropogate(MTreeNode node, int eval, boolean proven) {
		if (proven) node.lower = node.upper = eval;
		if (eval < MIN_EVAL) eval = MIN_EVAL;
		if (eval > MAX_EVAL) eval = MAX_EVAL;
		backpropogate(node, 1, eval, eval * eval, 0, proven);
	}

	private void backpropogate(MTreeNode node, int nvisit, int eval, int sumsq, int depth,
			boolean propogate_bound) {
		node.visits += nvisit;
		node.sum_utility += eval;
		node.sum_sq += sumsq;

		node.depth = Math.max(node.depth, depth);
		if (node.isMaxNode()) depth++;
		for (MTreeNode parent : node.parents) {
			boolean parent_propogate = propogate_bound;
			if (propogate_bound) parent_propogate = parent.setBounds();
			backpropogate(parent, nvisit, eval, sumsq, depth, parent_propogate);
		}
	}

	@Override
	public void cleanUp() {
		return;
	}
}

class HSimThread extends Thread {
	public static final MTreeNode HALT = new MTreeNode(null, null);

	public StateMachine machine;
	public Role role;
	public long timeout;
	public BlockingQueue<MTreeNode> input;
	public BlockingQueue<Integer> output;

	public HSimThread(StateMachine machine, Role role, long timeout, BlockingQueue<MTreeNode> input,
			BlockingQueue<Integer> output) {
		this.machine = machine;
		this.role = role;
		this.timeout = timeout;
		this.input = input;
		this.output = output;
	}

	private int simulate(MTreeNode node)
			throws MoveDefinitionException, TransitionDefinitionException, GoalDefinitionException {
		MachineState state = node.state;
		if (node.move != null) state = machine.getRandomNextState(state, role, node.move);
		while (!machine.isTerminal(state)) {
			if (System.currentTimeMillis() > timeout) return MCTS.FAIL;
			state = machine.getRandomNextState(state);
		}
		return machine.findReward(role, state);
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

class MTreeNode {
	// prior: sum squaers = 10000 so that stdev != 0
	public long visits = 0;
	public long sum_utility = 0;
	public long sum_sq = 10000;
	// bounds
	public int lower = MyPlayer.MIN_SCORE;
	public int upper = MyPlayer.MAX_SCORE;

	public List<MTreeNode> children = new ArrayList<>();
	public List<MTreeNode> parents = new ArrayList<>();

	public MachineState state;
	public Move move; // null if max-node; non-null if min-node
	public int depth = 0;

	public MTreeNode(MachineState state, Move move) {
		this.move = move;
		this.state = state;
	}

	public String info() {
		return String.format("%s score=%f bound=(%d, %d)", move, utility(), lower, upper);
	}

	public boolean setBounds() {
		int oldupp = upper, oldlow = lower;
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
		return putInBounds((double) sum_utility / visits);
	}

	// dynamic score: multiplies by standard deviation
	public double score(double c) {
		double util = (double) sum_utility / visits;
		double var = (double) sum_sq / visits - util * util;
		int sum_parent_visits = 0;
		for (MTreeNode parent : parents) {
			sum_parent_visits += parent.visits;
		}
		return putInBounds(util) + c * Math.sqrt(Math.log(sum_parent_visits) / visits * var);
	}
}

class MSimThread extends Thread {

	public StateMachine machine;
	public MTreeNode node;
	public Role role;
	public long timeout;
	public int result;

	public MSimThread(StateMachine machine, MTreeNode node, Role role, long timeout) {
		this.machine = machine;
		this.node = node;
		this.role = role;
		this.timeout = timeout;
		this.result = MCTS.FAIL;
	}

	@Override
	public void run() {
		try {
			MachineState state = node.state;
			if (node.move != null) state = machine.getRandomNextState(state, role, node.move);
			else state = state.clone();
			while (!machine.isTerminal(state)) {
				if (System.currentTimeMillis() > timeout) return; // FAIL
				state = machine.getRandomNextState(state);
			}
			int score = machine.findReward(role, state);
			result = score;
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
}

class MThread extends Thread {

	StateMachineGamer gamer;
	long timeout;
	ConcurrentLinkedQueue<Integer> data;

	public MThread(StateMachineGamer gamer, long timeout, ConcurrentLinkedQueue<Integer> data) {
		this.gamer = gamer;
		this.timeout = timeout;
		this.data = data;
	}

	@Override
	public void run() {
		Role role = gamer.getRole();
		StateMachine machine = gamer.getStateMachine();
		MachineState initial = machine.getInitialState();

		while (System.currentTimeMillis() < timeout) {
			try {
				int game = randomGame(machine, initial, role, timeout);
				if (game == MCTS.FAIL) break;
				data.add(game);
			} catch (Exception e) {
				e.printStackTrace();
			}

		}
	}

	private int randomGame(StateMachine machine, MachineState state, Role role, long timeout)
			throws MoveDefinitionException, GoalDefinitionException, TransitionDefinitionException {
		while (!machine.isTerminal(state)) {
			if (System.currentTimeMillis() > timeout) return MCTS.FAIL;
			state = machine.getRandomNextState(state);
		}
		return machine.findReward(role, state);
	}
}