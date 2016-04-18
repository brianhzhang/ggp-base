import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Queue;
import java.util.concurrent.ConcurrentLinkedQueue;

import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;

public class Heuristic extends Method {

	public static final int TIMEOUT_SCORE = MyPlayer.MIN_SCORE - 1;
	public static final int MIN_HEURISTIC = MyPlayer.MIN_SCORE + 1;
	public static final int MAX_HEURISTIC = MyPlayer.MAX_SCORE - 1;

	public static final int N_HEURISTIC = 3;
	public HeuristicFn[] heuristics = { this::mobility, this::goal, this::oppGoal };
	private double[] weights = new double[N_HEURISTIC];
	private double adjustment = 0;
	private boolean heuristicUsed = false;
	private List<Role> roles;

	private int period;

	@Override
	public void metaGame(StateMachineGamer gamer, long timeout) {
		ConcurrentLinkedQueue<HGameData> data = new ConcurrentLinkedQueue<>();
		List<HThread> threads = new ArrayList<HThread>();
		Role role = gamer.getRole();
		roles = new ArrayList<>(gamer.getStateMachine().findRoles());
		roles.remove(role);
		System.out.println("begin random exploration");
		for (int i = 0; i < MyPlayer.N_THREADS; i ++) {
			HThread t = new HThread(gamer, roles, timeout, this, data);
			threads.add(t);
			t.start();
		}
		for (int i = 0; i < MyPlayer.N_THREADS; i ++) {
			try {
				threads.get(i).join();
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
		
		int ngame = data.size();
		System.out.println("games analyzed: " + ngame);
		double[] goals = new double[ngame];
		double[][] totals = new double[N_HEURISTIC][ngame];
		int count = 0;
		while (!data.isEmpty()) {
			HGameData game = data.poll();
			goals[count] = game.goal;
			for (int j = 0; j < N_HEURISTIC; j++) {
				totals[j][count] = game.heuristics[j] / game.nstep;
			}
			count ++;
		}
		double tot_rsq = 0;
		adjustment = 0;
		for (int i = 0; i < N_HEURISTIC; i++) {
			Correlation c = Statistics.linreg(totals[i], goals);
			System.out.printf("component %d: g = %fx + %f, r^2=%f\n", i, c.m, c.b, c.rsq);
			weights[i] = c.m * c.rsq / 2; // dividing by 2 to counter the effect of averaging
			adjustment += c.b * c.rsq;
			tot_rsq += c.rsq;
		}
		for (int i = 0; i < N_HEURISTIC; i++) {
			weights[i] /= tot_rsq;
		}
		adjustment /= tot_rsq;
		System.out.printf("heuristic = %f + %s\n", adjustment, Arrays.toString(weights));
	}

	@Override
	public Move run(StateMachine machine, MachineState state, Role role, List<Move> moves,
			long timeout) throws GoalDefinitionException, MoveDefinitionException,
					TransitionDefinitionException {
		Move bestMove = moves.get(0);
		int bestScore = MyPlayer.MIN_SCORE;

		int level = 0;
		while (System.currentTimeMillis() < timeout) {
			level++;
			heuristicUsed = false;
			// alpha-beta heuristic: analyze previous best move first
			int score = minscore(machine, state, role, bestMove, MyPlayer.MIN_SCORE,
					MyPlayer.MAX_SCORE, level, timeout);
			if (score == TIMEOUT_SCORE) break;
			bestScore = score;
			for (Move move : moves) {
				if (move == bestMove) continue;
				score = minscore(machine, state, role, move, bestScore, MyPlayer.MAX_SCORE, level,
						timeout);
				if (score == TIMEOUT_SCORE) break;
				if (score > bestScore) {
					bestMove = move;
					bestScore = score;
					if (score == MyPlayer.MAX_SCORE) break;
				}
			}
			if (!heuristicUsed) break; // game fully analyzed
		}
		System.out.printf("bestmove=%s score=%d depth=%d\n", bestMove, bestScore, level);
		return bestMove;
	}

	private int maxscore(StateMachine machine, MachineState state, Role role, int alpha, int beta,
			int level, long timeout) throws GoalDefinitionException, MoveDefinitionException,
					TransitionDefinitionException {
		if (machine.isTerminal(state)) return machine.findReward(role, state);
		List<Move> actions = machine.findLegals(role, state);
		if (level <= 0) return heuristic(role, state, machine, actions);
		if (System.currentTimeMillis() > timeout) return TIMEOUT_SCORE;
		for (Move move : actions) {
			int score = minscore(machine, state, role, move, alpha, beta, level, timeout);
			if (score == TIMEOUT_SCORE) return score;
			alpha = Math.max(alpha, score);
			if (alpha >= beta) break;
		}
		return alpha;
	}

	// as seen in notes ch 6
	private int minscore(StateMachine machine, MachineState state, Role role, Move move, int alpha,
			int beta, int level, long timeout) throws GoalDefinitionException,
					MoveDefinitionException, TransitionDefinitionException {
		if (System.currentTimeMillis() > timeout) return TIMEOUT_SCORE;
		// use joint moves so that we can deal with n-player games; n != 2
		for (List<Move> jmove : machine.getLegalJointMoves(state, role, move)) {
			MachineState next = machine.getNextState(state, jmove);
			int score = maxscore(machine, next, role, alpha, beta, level - 1, timeout);
			if (score == TIMEOUT_SCORE) return score;
			beta = Math.min(beta, score);
			if (alpha >= beta) return alpha;
		}
		return beta;
	}

	@Override
	public void cleanUp() {

	}

	private int heuristic(Role role, MachineState state, StateMachine machine, List<Move> actions)
			throws MoveDefinitionException, GoalDefinitionException {
		heuristicUsed = true;
		double heuristic = adjustment;
		for (int i = 0; i < N_HEURISTIC; i++) {
			heuristic += weights[i] * heuristics[i].eval(role, state, machine, actions);
		}
		if (heuristic < MIN_HEURISTIC) return MIN_HEURISTIC;
		if (heuristic > MAX_HEURISTIC) return MAX_HEURISTIC;
		return (int) heuristic;
	}

	private double mobility(Role role, MachineState state, StateMachine machine,
			List<Move> actions) {
		return actions.size();
	}

	private double goal(Role role, MachineState state, StateMachine machine, List<Move> actions) {
		try {
			return machine.findReward(role, state);
		} catch (GoalDefinitionException e) {
			return MyPlayer.MIN_SCORE;
		}
	}

	private double oppGoal(Role role, MachineState state, StateMachine machine,
			List<Move> actions) {
		if (roles.isEmpty()) return 0;
		int sum = 0;
		for (Role opp : roles) {
			try {
				sum += machine.findReward(opp, state);
			} catch (GoalDefinitionException e) {
			}
		}
		return sum;
	}
}

class HThread extends Thread {
	
	StateMachineGamer gamer;
	List<Role> roles;
	long timeout;
	Heuristic h;
	ConcurrentLinkedQueue<HGameData> data;
	
	public HThread(StateMachineGamer gamer, List<Role> roles, long timeout, Heuristic h,
			ConcurrentLinkedQueue<HGameData> data2) {
		this.gamer = gamer;
		this.roles = roles;
		this.timeout = timeout;
		this.h = h;
		this.data = data2;
	}
	
	public void run() {
		Role role = gamer.getRole();
		StateMachine machine = gamer.getStateMachine();
		MachineState initial = machine.getInitialState();
		
		while (System.currentTimeMillis() < timeout) {
			HGameData game = null;
			try {
				game = randomGame(machine, initial, role, timeout);
			} catch (Exception e) {
				e.printStackTrace();
				continue;
			}
			if (game == null) break;
			data.add(game);
		}
	}
	
	private HGameData randomGame(StateMachine machine, MachineState state, Role role, long timeout)
			throws MoveDefinitionException, GoalDefinitionException, TransitionDefinitionException {
		HGameData ret = new HGameData();
		while (!machine.isTerminal(state)) {
			if (System.currentTimeMillis() > timeout) return null;
			ret.nstep++;
			List<Move> actions = machine.findLegals(role, state);
			if (actions.size() > 1) ret.nmove++;
			for (int i = 0; i < Heuristic.N_HEURISTIC; i++) {
				ret.heuristics[i] += h.heuristics[i].eval(role, state, machine, actions);
			}
			state = machine.getRandomNextState(state);
		}
		ret.goal = machine.findReward(role, state);
		return ret;
	}
}

class HGameData {
	public int nstep; // total number of steps
	public int nmove; // total number of times we had >1 legal moves
	public double[] heuristics = new double[Heuristic.N_HEURISTIC];
	public int goal;
}

interface HeuristicFn {
	public double eval(Role role, MachineState state, StateMachine machine, List<Move> actions);
}
