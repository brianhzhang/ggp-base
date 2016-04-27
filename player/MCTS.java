import java.util.ArrayList;
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

	public double breadth_inclination = 20000;

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
		double results[] = new double[ngame + 2];
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
		MTreeNode root = new MTreeNode(machine, state, null, null);
		while (System.currentTimeMillis() < timeout) {
			MTreeNode node = select(root);
			expand(machine, role, node);
			int eval = simulate(machine, node, role, timeout);
			if (eval == FAIL) break;
			backpropogate(node, eval);
		}
		double score = FAIL;
		MTreeNode best = null;
		for (MTreeNode child : root.children) {
			double newscore = child.utility();
			Log.printf("move=%s score=%f visits=%d\n", child.move, newscore, child.visits);
			if (newscore > score) {
				score = newscore;
				best = child;
			}
		}
		Log.printf("bestmove=%s score=%f visits=%d\n", best.move, score, root.visits);
		return best.move;
	}

	private MTreeNode select(MTreeNode node) {
		if (node.visits == 0 || node.isTerminal) return node;
		while (true) {
			for (MTreeNode child : node.children) {
				if (child.visits == 0 || child.isTerminal) return child;
			}
			MTreeNode best = null;
			if (node.move == null) { // max node
				double score = Integer.MIN_VALUE;
				for (MTreeNode child : node.children) {
					double newscore = child.score(breadth_inclination);
					if (newscore > score) {
						score = newscore;
						best = child;
					}
				}
			} else { // min node
				double score = Integer.MAX_VALUE;
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
			if (node.isTerminal) return;
			List<Move> actions = machine.findLegals(role, node.state);
			for (Move move : actions) {
				MTreeNode newnode = new MTreeNode(machine, node.state, move, node);
				node.children.add(newnode);
			}
		} else {
			List<List<Move>> actions = machine.getLegalJointMoves(node.state, role, node.move);
			for (List<Move> jmove : actions) {
				MachineState newstate = machine.findNext(jmove, node.state);
				MTreeNode newnode = new MTreeNode(machine, newstate, null, node);
				node.children.add(newnode);
			}
		}
	}

	private int simulate(StateMachine machine, MTreeNode node, Role role, long timeout)
			throws MoveDefinitionException, GoalDefinitionException, TransitionDefinitionException {
		MachineState state = node.state;
		if (node.move != null) state = machine.getRandomNextState(state, role, node.move);
		while (!machine.isTerminal(state)) {
			if (System.currentTimeMillis() > timeout) return FAIL;
			state = machine.getRandomNextState(state);
		}
		return machine.findReward(role, state);
	}

	private void backpropogate(MTreeNode node, int eval) {
		while (node != null) {
			node.visits++;
			node.sum_utility += eval;
			node = node.parent;
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
	public List<MTreeNode> children = new ArrayList<>();
	public MTreeNode parent;
	public boolean isTerminal;

	public MachineState state;
	public Move move; // null if max-node; non-null if min-node

	public MTreeNode(StateMachine machine, MachineState state, Move move, MTreeNode parent) {
		this.parent = parent;
		this.move = move;
		this.state = state;
		this.isTerminal = move == null && machine.isTerminal(state);
	}

	public double utility() {
		return (double) sum_utility / visits;
	}

	public double score(double c) {
		return utility() + c * Math.sqrt(Math.log(parent.visits) / visits);
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