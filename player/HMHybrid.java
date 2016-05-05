import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;

import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.gdl.grammar.Gdl;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;

public class HMHybrid extends Method {

	public static final int FAIL = MyPlayer.MIN_SCORE - 1;
	private static final double CFACTOR = 1.0;
	private List<MTreeNode> cache = new ArrayList<>();
	private StateMachine[] machines;
	private boolean propNetInitialized = false;
	private MyPlayer gamer;

	private StateMachineCreatorThread smthread;

	private class StateMachineCreatorThread extends Thread {
		private List<Gdl> description;
		public MetaPropNetStateMachineFactory m;

		public StateMachineCreatorThread(List<Gdl> description) {
			this.description = description;
		}

		@Override
		public void run() {
			m = new MetaPropNetStateMachineFactory(description);
			Log.println("Propnets ready");
		}
	}

	// if the metapropnetstatemachinefactory has finished, update the machines
	private boolean checkStateMachineStatus() {
		if (!propNetInitialized && !smthread.isAlive()) {
			gamer.switchToPropnets(smthread.m, machines);
			Log.println("Propnets initialized");
			return propNetInitialized = true;
		}
		return false;
	}

	public HMHybrid(MyPlayer gamer, List<Gdl> description) {
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
		try {
			smthread.join(timeout - System.currentTimeMillis());
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		if (!checkStateMachineStatus()) Log.println("Still building propnet...");
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
		if (root == null) {
			root = new MTreeNode(rootstate, null, null);
			expand(machine, role, root);
		}
		root.parent = null;
		HSimThread[] threads = new HSimThread[MyPlayer.N_THREADS];
		BlockingQueue<MTreeNode> input = new LinkedBlockingQueue<>();
		BlockingQueue<Integer> output = new LinkedBlockingQueue<>();
		for (int i = 0; i < MyPlayer.N_THREADS; i++) {
			threads[i] = new HSimThread(machines[i], role, timeout, input, output);
			threads[i].start();
		}
		while (System.currentTimeMillis() < timeout) {
			if (root.isProven()) break;
			MTreeNode node = select(root);
			if (machine.isTerminal(node.state)) {
				backpropogate(node, machine.findReward(role, node.state), 0, true);
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
						backpropogate(node, eval, 0, false);
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

	private void backpropogate(MTreeNode node, int eval, int depth, boolean proven) {
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
}

class HSimThread extends Thread {
	public static final MTreeNode HALT = new MTreeNode(null, null, null);

	public StateMachine machine;
	public Role role;
	public long timeout;
	public BlockingQueue<MTreeNode> input;
	public BlockingQueue<Integer> output;
	public static final int MAX_SCORE = 99;
	public static final int MIN_SCORE = 1;

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
		int score = machine.findReward(role, state);
		if (score > MAX_SCORE) return MAX_SCORE;
		else if (score < MIN_SCORE) return MIN_SCORE;
		else return score;
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