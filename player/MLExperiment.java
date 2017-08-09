import java.util.*;

import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;

public class MLExperiment extends Method {

	public static final int FAIL = MyPlayer.MIN_SCORE - 1;
	public static final int MIN_HEURISTIC = MyPlayer.MIN_SCORE + 1;
	public static final int MAX_HEURISTIC = MyPlayer.MAX_SCORE - 1;

	public static final int N_HEURISTIC = 4;

	// metagaming results
	protected double[] weights = new double[N_HEURISTIC];
	protected double adjustment = 0;
	protected int period; // one less than the period; i.e. if we make every move then period = 0

	protected List<Role> opps;
	protected Map<MachineState, HCacheEnt> cache;

	private boolean heuristicUsed = false;

	private int nNodes;
	private int nCacheHits;

	JustKiddingPropNetStateMachine machine;
	AYearLaterMachineLearningPropNet pileOfML;

	MyPlayer gamer;
//	int[] modelShape = {150, 150, 150};
	double loss = 0;
	int losscount = 0;

	Random gen;

	@Override
	public void metaGame(StateMachineGamer gamer, long timeout) {
		cache = new HashMap<MachineState, HCacheEnt>();
		gen = new Random();

		this.gamer = (MyPlayer) gamer;
		machine = new JustKiddingPropNetStateMachine();
		machine.initialize(this.gamer.gameDescription);
		pileOfML = new AYearLaterMachineLearningPropNet();
		pileOfML.initialize(machine.p);
		gamer.role = gamer.getRole();
		gamer.currentState = machine.getInitialState();
		gamer.stateMachine = machine;

		int count = 0;
		Log.println("begin random exploration");
		PropNetMachineState init = (PropNetMachineState) machine.getInitialState();
		for(int i = 0; System.currentTimeMillis() - timeout > MyPlayer.TIMEOUT_BUFFER; i ++) {
			try {
				trainOnce(init, i);
			} catch (TransitionDefinitionException | MoveDefinitionException | GoalDefinitionException e) {
				e.printStackTrace();
			}
			count ++;
		}
		Log.println(count + " games explored");
	}

	private void trainOnce(PropNetMachineState init, int count)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		ArrayList<PropNetMachineState> states = new ArrayList<PropNetMachineState>();
		PropNetMachineState current = init;
		while (!machine.isTerminal(current)) {
			current = (PropNetMachineState) machine.getNextState(current, machine.getRandomJointMove(current));
			states.add(current);
		}
		double[] results = machine.getAllGoals(current);
		loss += pileOfML.trainOnce(states.get(gen.nextInt(states.size())), machine, results); //CHANGED FOR TESTING xxxxxxx
		losscount ++;
		if ((count + 1) % 1000 == 0) {
			Log.println("loss: " + (loss/losscount));
			losscount = 0;
			loss = 0;
		}
	}

	@Override
	public Move run(StateMachine machine, MachineState state, Role role, List<Move> moves, long timeout)
			throws GoalDefinitionException, MoveDefinitionException, TransitionDefinitionException {
		Log.println("--------------------");
		System.out.println(state.getClass());
		System.out.println(machine.getClass());
		moves = new ArrayList<>(moves);
		Collections.shuffle(moves);
		Move bestMove = moves.get(0);
		double bestScore = MyPlayer.MIN_SCORE;

		int level;
		HCacheEnt baseEnt = cache.get(state);
		if (baseEnt == null) level = 0;
		else level = baseEnt.depth;
		int startLevel = level;
		nNodes = nCacheHits = 0;
		if (moves.size() > 1) {
			while (System.currentTimeMillis() < timeout) {
				heuristicUsed = false;
				// alpha-beta heuristic: analyze previous best move first
				double score = minscore(machine, state, role, bestMove, MyPlayer.MIN_SCORE,
						MyPlayer.MAX_SCORE, level, timeout);
				if (score == FAIL) break;
				bestScore = score;
				for (Move move : moves) {
					if (move == bestMove) continue;
					score = minscore(machine, state, role, move, bestScore, MyPlayer.MAX_SCORE,
							level,
							timeout);
					if (score == FAIL) break;
					if (score > bestScore) {
						bestMove = move;
						bestScore = score;
						if (score == MyPlayer.MAX_SCORE) break;
					}
				}
				if (!heuristicUsed && startLevel != level) break; // game fully analyzed
				//if (level == 5) break; // limit depth
				Log.printf("bestmove=%s score=%f depth=%d nodes=%d cachehits=%d cachesize=%d\n",
						bestMove, bestScore, level, nNodes, nCacheHits, cache.size());
				level++;

			}
		}
		Log.printf("played=%s score=%f depth=%d nodes=%d cachehits=%d cachesize=%d\n", bestMove,
				bestScore, level, nNodes, nCacheHits, cache.size());
		return bestMove;
	}

	private double maxscore(StateMachine machine, MachineState state, Role role, double alpha, double beta,
			int level, long timeout) throws GoalDefinitionException, MoveDefinitionException,
	TransitionDefinitionException {
		if (System.currentTimeMillis() > timeout) return FAIL;
		nNodes++;
		if (machine.isTerminal(state)) {
			return machine.findReward(role, state);}
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
		if (level <= 0) {
			//xxxxxxx NOTE TO LATER, THIS IS THE MAIN DIFFERENCE FROM HEURISTIC PLAYER
			double heuristic = 0;
			heuristic += pileOfML.forwardPass((PropNetMachineState) state,
					(JustKiddingPropNetStateMachine) machine)[machine.getRoles().indexOf(gamer.getRole())];
			heuristicUsed = true;
			return heuristic;
		}
		if (cacheEnt == null) {
			cacheEnt = new HCacheEnt();
			cache.put(state, cacheEnt);
		}

		double a = alpha;
		for (Move move : actions) {
			double score = minscore(machine, state, role, move, a, beta, level, timeout);
			if (score == FAIL) return score;
			a = Math.max(a, score);
			if (a >= beta) break;
		}
		if (level >= cacheEnt.depth) {
			if (a < beta) cacheEnt.upper = a;
			if (a > alpha) cacheEnt.lower = a;
			cacheEnt.depth = level;
		}
		return a;
	}

	// as seen in notes ch 6
	private double minscore(StateMachine machine, MachineState state, Role role, Move move, double alpha,
			double beta, int level, long timeout) throws GoalDefinitionException,
	MoveDefinitionException, TransitionDefinitionException {
		if (System.currentTimeMillis() > timeout) return FAIL;
		// use joint moves so that we can deal with n-player games; n != 2
		for (List<Move> jmove : machine.getLegalJointMoves(state, role, move)) {
			MachineState next = machine.getNextState(state, jmove);
			double score = maxscore(machine, next, role, alpha, beta, level - 1, timeout);
			if (score == FAIL) return score;
			beta = Math.min(beta, score);
			if (alpha >= beta) return alpha;
		}
		return beta;
	}


	@Override
	public void cleanUp() {
		//		jep.close();
	}

	private class HCacheEnt {
		public double lower = MyPlayer.MIN_SCORE;
		public double upper = MyPlayer.MAX_SCORE;
		public int depth = Integer.MIN_VALUE;
	}
}