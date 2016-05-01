import java.util.ArrayList;
import java.util.Arrays;
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

public class HMHybrid extends Heuristic {
	private boolean useMC;

	private double breadth_inclination = 20000;
	private List<MTreeNode> cache = new ArrayList<>();

	@Override
	public void metaGame(StateMachineGamer gamer, long timeout) {
		ConcurrentLinkedQueue<HGameData> data = new ConcurrentLinkedQueue<>();
		List<HThread> threads = new ArrayList<HThread>();
		Role role = gamer.getRole();
		opps = new ArrayList<>(gamer.getStateMachine().findRoles());
		opps.remove(role);
		Log.println("");
		Log.println("begin random exploration");
		for (int i = 0; i < MyPlayer.N_THREADS; i++) {
			HThread t = new HThread(gamer, opps, timeout, this, data, goalProps);
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
		Log.println("games analyzed: " + ngame);
		double[] goals = new double[ngame];
		double[][] totals = new double[N_HEURISTIC][ngame];
		HGameData[] games = new HGameData[ngame];
		int count = 0;
		int movetot = 0;
		int steptot = 0;
		while (!data.isEmpty()) {
			HGameData game = games[count] = data.poll();
			goals[count] = game.goal;
			for (int j = 0; j < N_HEURISTIC; j++) {
				totals[j][count] = game.heuristics[j] / game.nstep;
			}
			count++;
			steptot += game.nstep;
			movetot += game.nmove;
		}
		period = (int) Math.round(1.0 * steptot / movetot);
		Log.printf("total steps %d / our moves %d = period %d\n", steptot, movetot, period);
		double tot_rsq = 0;
		adjustment = 0;
		Correlation[] c = new Correlation[N_HEURISTIC];
		for (int i = 0; i < N_HEURISTIC; i++) {
			c[i] = Statistics.linreg(totals[i], goals);
			Log.printf("component %d: g = %fx + %f, r^2=%f\n", i, c[i].m, c[i].b, c[i].rsq);
			tot_rsq += c[i].rsq;
		}
		double old_tot = tot_rsq;
		tot_rsq = 0;
		double max_rsq = 0;
		for (int i = 0; i < N_HEURISTIC; i++) {
			if (c[i].rsq / old_tot < 0.1) c[i].m = c[i].b = c[i].rsq = 0;
			weights[i] = c[i].m * c[i].rsq / 2; // dividing by 2 to counter the effect of averaging
			adjustment += c[i].b * c[i].rsq;
			tot_rsq += c[i].rsq;
			max_rsq = Math.max(max_rsq, c[i].rsq);
		}
		for (int i = 0; i < N_HEURISTIC; i++) {
			weights[i] /= tot_rsq;
		}
		adjustment /= tot_rsq;
		Log.printf("heuristic = %f + %s\n", adjustment, Arrays.toString(weights));

		double[] avgheuristic = new double[ngame];
		for (int i = 0; i < ngame; i++) {
			avgheuristic[i] = adjustment;
			for (int j = 0; j < N_HEURISTIC; j++) {
				avgheuristic[i] += weights[j] * games[i].heuristics[j] / games[i].nstep;
			}
		}

		Log.printf("tot r^2 = %f\n", max_rsq);
		useMC = max_rsq < 0.5;

		double[] results = new double[ngame + 2];
		System.arraycopy(useMC ? goals : avgheuristic, 0, results, 0, ngame);
		results[ngame] = MyPlayer.MIN_SCORE;
		results[ngame + 1] = MyPlayer.MAX_SCORE;

		double std = Statistics.stdev(results);

		Log.println("goal mean: " + Statistics.mean(results));
		Log.println("goal std: " + std);
		// the std of a game that randomly ends with either 0 or 100 is 50.
		// if this game should use a constant of 100 sqrt(2), then multiply std by sqrt 8
		Log.println("breadth inclination: " + (breadth_inclination = Math.sqrt(8) * std));

		Log.println("eval method: " + (useMC ? "monte carlo" : "heuristic"));
	}

	@Override
	public Move run(StateMachine machine, MachineState rootstate, Role role, List<Move> moves,
			long timeout) throws GoalDefinitionException, MoveDefinitionException,
					TransitionDefinitionException {
		long timestart = System.currentTimeMillis();
		long simtime = 0;

		Log.println("--------------------");
		// set up tree
		MTreeNode root = null;
		for (MTreeNode node : cache) {
			if (node.state.equals(rootstate)) {
				System.out.printf("cache retrieval: nodes=%d depth=%d\n", node.visits, node.depth);
				root = node;
				break;
			}
		}
		cache.clear();
		if (root == null) {
			root = new MTreeNode(rootstate, null, null);
			expand(machine, role, root);
		}
		Collections.shuffle(root.children);
		root.parent = null;
		while (System.currentTimeMillis() < timeout) {
			if (root.isProven()) break;
			MTreeNode node = select(root);
			if (machine.isTerminal(node.state)) {
				backpropogate(node, machine.findReward(role, node.state), 0, true);
			} else {
				expand(machine, role, node);
				MSimThread[] threads = new MSimThread[MyPlayer.N_THREADS];
				if (useMC) {
					for (int i = 0; i < MyPlayer.N_THREADS; i++) {
						threads[i] = new MSimThread(machine, node, role, timeout);
						threads[i].start();
					}
					long start = System.currentTimeMillis();
					for (int i = 0; i < MyPlayer.N_THREADS; i++) {
						try {
							threads[i].join();
						} catch (InterruptedException e) {
							e.printStackTrace();
						}
						int eval = threads[i].result;
						if (eval == FAIL) continue;
						backpropogate(node, eval, 0, false);
					}
					simtime += System.currentTimeMillis() - start;
				} else {
					List<Move> legals = machine.findLegals(role, node.state);
					backpropogate(node, heuristic(role, node.state, machine, legals), 0, false);
				}
			}
		}
		MTreeNode bestChild = null;
		for (MTreeNode child : root.children) {
			if (bestChild == null || child.utility() > bestChild.utility()) bestChild = child;
			System.out.println("move=" + info(child, child));
		}
		for (MTreeNode child : bestChild.children) {
			cache.add(child);
		}
		System.out.println("played=" + info(bestChild, root));
		System.out.println("total time = " + (System.currentTimeMillis() - timestart));
		System.out.println("time spent on sims = " + simtime);
		return bestChild.move;
	}

	private String info(MTreeNode scoreNode, MTreeNode rootNode) {
		return String.format("%s score=%f bound=(%d, %d) nodes=%d depth=%d", scoreNode.move,
				scoreNode.utility(), scoreNode.lower, scoreNode.upper, rootNode.visits,
				rootNode.depth);
	}

	private MTreeNode select(MTreeNode node) {
		while (true) {
			if (node.children.isEmpty()) return node;
			for (MTreeNode child : node.children) {
				if (child.visits == 0) return child;
			}
			MTreeNode best = null;
			if (node.isMaxNode()) { // max node
				double score = Double.NEGATIVE_INFINITY;
				for (MTreeNode child : node.children) {
					if (child.isProven()) continue;
					double newscore = child.score(breadth_inclination);
					if (newscore > score) {
						score = newscore;
						best = child;
					}
				}
			} else { // min node
				double score = Double.POSITIVE_INFINITY;
				for (MTreeNode child : node.children) {
					if (child.isProven()) continue;
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
		if (node.isMaxNode()) { // max-node
			if (machine.isTerminal(node.state)) {
				System.err.println("Asked to expand terminal state...");
				return;
			}
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

	private void backpropogate(MTreeNode node, int eval, int depth, boolean proven) {
		if (proven) {
			node.lower = node.upper = eval;
		}
		while (true) {
			node.visits++;
			node.sum_utility += eval;
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
