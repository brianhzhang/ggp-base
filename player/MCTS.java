import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.ConcurrentLinkedQueue;

import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;

public class MCTS extends Method {
	public static final int FAIL = MyPlayer.MIN_SCORE - 1;

	private double breadth_inclination = 20000;
	private List<MTreeNode> cache = new ArrayList<>();

	@Override
	public void metaGame(StateMachineGamer gamer, long timeout) {

		ConcurrentLinkedQueue<Integer> data = new ConcurrentLinkedQueue<>();
		List<MThread> threads = new ArrayList<MThread>();

		Log.println("");
		Log.println("begin random exploration");
		for (int i = 0; i < MyPlayer.N_THREADS; i++) {
			MThread t = new MThread(gamer, timeout, data);
			threads.add(t);
			t.start();
		}
		for (int i = 0; i < MyPlayer.N_THREADS; i++) {
			try {
				threads.get(i).join();
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}

		int ngame = data.size();
		double[] results = new double[ngame + 2];
		for (int i = 0; i < ngame; i++) {
			results[i] = data.poll();
		}
		results[ngame] = MyPlayer.MIN_SCORE;
		results[ngame + 1] = MyPlayer.MAX_SCORE;
		// as a prior, so that variance is never 0

		Log.println("games analyzed: " + ngame);
		double std = Statistics.stdev(results);
		Log.println("goal mean: " + Statistics.mean(results));
		Log.println("goal std: " + std);
		// the std of a game that randomly ends with either 0 or 100 is 50.
		// if this game should use a constant of 100 sqrt(2), then we must multiply std by sqrt 8
		Log.println("breadth inclination: " + (breadth_inclination = Math.sqrt(8) * std));
	}

	@Override
	public Move run(StateMachine machine, MachineState state, Role role, List<Move> moves,
			long timeout) throws GoalDefinitionException, MoveDefinitionException,
					TransitionDefinitionException {
		Log.println("--------------------");
		// set up tree
		MTreeNode root = null;
		for (MTreeNode node : cache) {
			if (node.state.equals(state)) {
				System.out.printf("cache retrieval: nodes=%d depth=%d\n", node.visits, node.depth);
				root = node;
				break;
			}
		}
		cache.clear();
		if (root == null) {
			root = new MTreeNode(state, null, null);
			expand(machine, role, root);
		}
		Collections.shuffle(root.children);
		while (System.currentTimeMillis() < timeout) {
			MTreeNode node = select(root);
			expand(machine, role, node);
			MSimThread[] threads = new MSimThread[MyPlayer.N_THREADS];
			for (int i = 0; i < MyPlayer.N_THREADS; i++) {
				threads[i] = new MSimThread(machine, node, role, timeout);
				threads[i].start();
			}
			for (int i = 0; i < MyPlayer.N_THREADS; i++) {
				try {
					threads[i].join();
				} catch (InterruptedException e) {
					e.printStackTrace();
				}
				int eval = threads[i].result;
				if (eval == FAIL) continue;
				backpropogate(node, eval, 0);
			}
		}
		MTreeNode bestChild = null;
		for (MTreeNode child : root.children) {
			if (bestChild == null || child.utility() > bestChild.utility()) bestChild = child;
			System.out.printf("move=%s score=%f nodes=%d depth=%d\n", child.move, child.utility(),
					child.visits, child.depth);
		}
		for (MTreeNode child : bestChild.children) {
			cache.add(child);
		}
		System.out.printf("played=%s score=%f nodes=%d depth=%d\n", bestChild.move,
				bestChild.utility(), root.visits, root.depth);
		return bestChild.move;
	}

	private MTreeNode select(MTreeNode node) {
		while (true) {
			if (node.children.isEmpty()) return node;
			for (MTreeNode child : node.children) {
				if (child.visits == 0) return child;
			}
			MTreeNode best = null;
			if (node.move == null) { // max node
				double score = Double.NEGATIVE_INFINITY;
				for (MTreeNode child : node.children) {
					double newscore = child.score(breadth_inclination);
					if (newscore > score) {
						score = newscore;
						best = child;
					}
				}
			} else { // min node
				double score = Double.POSITIVE_INFINITY;
				for (MTreeNode child : node.children) {
					double newscore = child.score(-breadth_inclination);
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
		if (node.move == null) { // max-node
			if (machine.isTerminal(node.state)) return;
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
	}

	private void backpropogate(MTreeNode node, int eval, int depth) {
		while (node != null) {
			node.visits++;
			node.sum_utility += eval;
			node.depth = Math.max(node.depth, depth);
			node = node.parent;
			depth++;
		}
	}

	@Override
	public void cleanUp() {
		return;
	}
}

class MTreeNode {
	public int visits = 0;
	public int sum_utility = 0;
	// bounds
	public int lower = MyPlayer.MIN_SCORE;
	public int upper = MyPlayer.MAX_SCORE;

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

	public double score(double c) {
		return utility() + c * Math.sqrt(Math.log(parent.visits) / visits);
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
			result = machine.findReward(role, state);
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