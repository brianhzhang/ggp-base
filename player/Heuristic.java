import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentLinkedQueue;

import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.gdl.grammar.GdlSentence;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;

public class Heuristic extends Method {

	public static final int FAIL = MyPlayer.MIN_SCORE - 1;
	public static final int MIN_HEURISTIC = MyPlayer.MIN_SCORE + 1;
	public static final int MAX_HEURISTIC = MyPlayer.MAX_SCORE - 1;

	public static final int N_HEURISTIC = 4;

	// metagaming results
	protected HeuristicFn[] heuristics = { this::mobility, this::oppMobility, this::goal,
			this::oppGoal};
	protected double[] weights = new double[N_HEURISTIC];
	protected double adjustment = 0;
	protected int period; // one less than the period; i.e. if we make every move then period = 0

	protected List<Role> opps;
	protected Map<MachineState, HCacheEnt> cache;

	private boolean heuristicUsed = false;

	private int nNodes;
	private int nCacheHits;

	private List<Double> mobility;
	private List<Double> oppMobility;

	// For goal
	protected ConcurrentHashMap<GdlSentence, HGoalProp> goalProps = new ConcurrentHashMap<GdlSentence, HGoalProp>();

	@Override
	public void metaGame(StateMachineGamer gamer, long timeout) {
		cache = new HashMap<>();
		ConcurrentLinkedQueue<HGameData> data = new ConcurrentLinkedQueue<>();
		List<HThread> threads = new ArrayList<HThread>();
		Role role = gamer.getRole();
		opps = new ArrayList<>(gamer.getStateMachine().findRoles());
		opps.remove(role);
		heuristics[0] = this::mobility;
		heuristics[1] = this::oppMobility;

		Log.println("");
		Log.println("begin random exploration");
		for (int i = 0; i < MyPlayer.N_THREADS; i++) {
			HThread t = new HThread(gamer, opps, timeout, this, gamer.getStateMachine(), data, goalProps);
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
		int count = 0;
		int movetot = 0;
		int steptot = 0;
		while (!data.isEmpty()) {
			HGameData game = data.poll();
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
		for (int i = 0; i < N_HEURISTIC; i++) {
			if (c[i].rsq / old_tot < 0.1) c[i].m = c[i].b = c[i].rsq = 0;
			weights[i] = c[i].m * c[i].rsq / 2; // dividing by 2 to counter the effect of averaging
			adjustment += c[i].b * c[i].rsq;
			tot_rsq += c[i].rsq;
		}
		for (int i = 0; i < N_HEURISTIC; i++) {
			weights[i] /= tot_rsq;
		}
		adjustment /= tot_rsq;
		heuristics[0] = this::avgMobility;
		heuristics[1] = this::avgOppMobility;
		Log.printf("heuristic = %f + %s\n", adjustment, Arrays.toString(weights));
	}

	@Override
	public Move run(StateMachine machine, MachineState state, Role role, List<Move> moves,
			long timeout) throws GoalDefinitionException, MoveDefinitionException,
					TransitionDefinitionException {
		// if (moves.size() == 1) return moves.get(0);
		Log.println("--------------------");

		Move bestMove = moves.get(0);
		int bestScore = MyPlayer.MIN_SCORE;

		int level;
		HCacheEnt baseEnt = cache.get(state);
		if (baseEnt == null) level = 0;
		else level = baseEnt.depth;
		int startLevel = level;
		nNodes = nCacheHits = 0;
		mobility = new ArrayList<>();
		oppMobility = new ArrayList<>();
		while (System.currentTimeMillis() < timeout) {
			heuristicUsed = false;
			// alpha-beta heuristic: analyze previous best move first
			int score = minscore(machine, state, role, bestMove, MyPlayer.MIN_SCORE,
					MyPlayer.MAX_SCORE, level, timeout);
			if (score == FAIL) break;
			bestScore = score;
			for (Move move : moves) {
				if (move == bestMove) continue;
				score = minscore(machine, state, role, move, bestScore, MyPlayer.MAX_SCORE, level,
						timeout);
				if (score == FAIL) break;
				if (score > bestScore) {
					bestMove = move;
					bestScore = score;
					if (score == MyPlayer.MAX_SCORE) break;
				}
			}
			if (!heuristicUsed && startLevel != level) break; // game fully analyzed
			Log.printf("bestmove=%s score=%d depth=%d nodes=%d cachehits=%d cachesize=%d\n",
					bestMove, bestScore, level, nNodes, nCacheHits, cache.size());
			level++;
		}
		Log.printf("played=%s score=%d depth=%d nodes=%d cachehits=%d cachesize=%d\n", bestMove,
				bestScore, level, nNodes, nCacheHits, cache.size());
		return bestMove;
	}

	private int maxscore(StateMachine machine, MachineState state, Role role, int alpha, int beta,
			int level, long timeout) throws GoalDefinitionException, MoveDefinitionException,
					TransitionDefinitionException {
		if (System.currentTimeMillis() > timeout) return FAIL;
		nNodes++;
		if (machine.isTerminal(state)) return machine.findReward(role, state);
		HCacheEnt cacheEnt = cache.get(state);
		if (cacheEnt != null && cacheEnt.depth >= level) {
			nCacheHits++;
			if (cacheEnt.lower >= beta) return beta;
			if (cacheEnt.upper <= alpha) return alpha;
			if (cacheEnt.lower == cacheEnt.upper) return cacheEnt.lower;
			alpha = Math.max(alpha, cacheEnt.lower);
			beta = Math.min(beta, cacheEnt.upper);
		}
		List<Move> actions = machine.findLegals(role, state);
		mobility.add(mobility(role, state, machine, actions));
		oppMobility.add(oppMobility(role, state, machine, actions));
		if (level <= 0) {
			int heuristic = heuristic(role, state, machine, actions);
			mobility.remove(mobility.size() - 1);
			oppMobility.remove(oppMobility.size() - 1);
			return heuristic;
		}
		if (cacheEnt == null) {
			cacheEnt = new HCacheEnt();
			cache.put(state, cacheEnt);
		}

		int a = alpha;
		for (Move move : actions) {
			int score = minscore(machine, state, role, move, a, beta, level, timeout);
			if (score == FAIL) return score;
			a = Math.max(a, score);
			if (a >= beta) break;
		}
		if (level >= cacheEnt.depth) {
			if (a < beta) cacheEnt.upper = a;
			if (a > alpha) cacheEnt.lower = a;
			cacheEnt.depth = level;
		}
		mobility.remove(mobility.size() - 1);
		oppMobility.remove(oppMobility.size() - 1);
		return a;
	}

	// as seen in notes ch 6
	private int minscore(StateMachine machine, MachineState state, Role role, Move move, int alpha,
			int beta, int level, long timeout) throws GoalDefinitionException,
					MoveDefinitionException, TransitionDefinitionException {
		if (System.currentTimeMillis() > timeout) return FAIL;
		// use joint moves so that we can deal with n-player games; n != 2
		for (List<Move> jmove : machine.getLegalJointMoves(state, role, move)) {
			MachineState next = machine.getNextState(state, jmove);
			int score = maxscore(machine, next, role, alpha, beta, level - 1, timeout);
			if (score == FAIL) return score;
			beta = Math.min(beta, score);
			if (alpha >= beta) return alpha;
		}
		return beta;
	}

	@Override
	public void cleanUp() {

	}

	protected int heuristic(Role role, MachineState state, StateMachine machine, List<Move> actions)
			throws MoveDefinitionException, GoalDefinitionException {
		heuristicUsed = true;
		double heuristic = adjustment;
		for (int i = 0; i < N_HEURISTIC; i++) {
			if (weights[i] == 0) continue;
			heuristic += weights[i] * heuristics[i].eval(role, state, machine, actions);
		}
		if (heuristic < MIN_HEURISTIC) return MIN_HEURISTIC;
		if (heuristic > MAX_HEURISTIC) return MAX_HEURISTIC;
		return (int) heuristic;
	}

	private double avgMobility(Role role, MachineState state, StateMachine machine,
			List<Move> actions) {
		double total = 0;
		for (int i = Math.max(0, mobility.size() - period); i < mobility.size(); i++) {
			total += mobility.get(i);
		}
		return total / period;
	}

	private double avgOppMobility(Role role, MachineState state, StateMachine machine,
			List<Move> actions) {
		double total = 0;
		for (int i = Math.max(0, oppMobility.size() - period); i < oppMobility.size(); i++) {
			total += oppMobility.get(i);
		}
		return total / period;
	}

	protected double mobility(Role role, MachineState state, StateMachine machine,
			List<Move> actions) {
		return actions.size();
	}

	protected double oppMobility(Role role, MachineState state, StateMachine machine,
			List<Move> actions) {
		int tot_moves = 1;
		for (Role opp : opps) {
			try {
				tot_moves *= machine.findLegals(opp, state).size();
			} catch (MoveDefinitionException e) {
				e.printStackTrace();
			}
		}
		return tot_moves;
	}

	protected double goal(Role role, MachineState state, StateMachine machine, List<Move> actions) {
		try {
			return machine.findReward(role, state);
		} catch (GoalDefinitionException e) {
			return MyPlayer.MIN_SCORE;
		}
	}

	protected double oppGoal(Role role, MachineState state, StateMachine machine,
			List<Move> actions) {
		if (opps.isEmpty()) return 0;
		int sum = 0;
		for (Role opp : opps) {
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
	private ConcurrentHashMap<GdlSentence, HGoalProp> goalProps;
	StateMachine machine;

	public HThread(StateMachineGamer gamer, List<Role> roles, long timeout, Heuristic h,
			StateMachine machine, ConcurrentLinkedQueue<HGameData> data2,
			ConcurrentHashMap<GdlSentence, HGoalProp> goalProps) {
		this.gamer = gamer;
		this.roles = roles;
		this.timeout = timeout;
		this.h = h;
		this.data = data2;
		this.machine = machine;
		this.goalProps = goalProps;
	}

	@Override
	public void run() {
		Role role = gamer.getRole();
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

class HGoalProp {
	public int totalScore;
	public int count;

	public HGoalProp(int totalScore, int count) {
		this.totalScore = totalScore;
		this.count = count;
	}
}

class HCacheEnt {
	public int lower = MyPlayer.MIN_SCORE;
	public int upper = MyPlayer.MAX_SCORE;
	public int depth = Integer.MIN_VALUE;
}
