import java.awt.GridLayout;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.concurrent.LinkedBlockingQueue;

import org.ggp.base.apps.player.config.ConfigPanel;
import org.ggp.base.player.gamer.exception.GamePreviewException;
import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.game.Game;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.cache.CachedStateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;
import org.ggp.base.util.statemachine.implementation.prover.ProverStateMachine;


public class MyPlayer extends StateMachineGamer {

	public final static int MAX_SCORE = 100;
	public final static int MIN_SCORE = 0;
	public static final int LEGAL = 1;
	public static final int RANDOM = 2;
	public static final int ALPHABETA = 3;

	public static final int N_THREADS = 4;
	private static final int N_EXPAND = 10;

	public int method = RANDOM;
	public static final int N_OPTIONS = 10;

	@Override
	public StateMachine getInitialStateMachine() {
		return new CachedStateMachine(new ProverStateMachine());
	}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {
		return;
	}

	@Override
	public Move stateMachineSelectMove(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {
		StateMachine machine = getStateMachine();
		MachineState state = getCurrentState();
		Role role = getRole();

		List<Move> moves = machine.findLegals(role, state);

		/** legal player **/
		// legal player #1: 8432
		// legal player #2: 1344
		if (method == LEGAL) {
			return moves.get(0);
		}
		/** random player **/
		// random player #1: 6920
		// random player #2: 1344
		// Random random = new Random();
		else if (method == RANDOM) {
			Random random = new Random();
			return moves.get(random.nextInt(moves.size())); // random player
		}

		/** alpha beta player **/
		// alpha beta #1: 7234
		// alpha beta #2: 4325
		else if (method == ALPHABETA) {
			if (moves.size() == 1) return moves.get(0);
			BestMove bestMove = new BestMove();
			bestMove.m = null;
			bestMove.score = MIN_SCORE;

			LinkedBlockingQueue<Work> work = new LinkedBlockingQueue<Work>();
			expandMoves(moves, work, machine, state, role);

			Set<Thread> threads = new HashSet<Thread>();
			for (int i = 0; i < N_THREADS; i ++) {
				AlphaBetaThread t = new AlphaBetaThread(work, machine, role, bestMove);
				t.start();
				threads.add(t);
			}
			joinAll(threads);
			System.out.println(bestMove.score);
			return bestMove.m;
		}
		else {
			return moves.get(0);
		}
	}

	private void expandMoves(List<Move> moves, LinkedBlockingQueue<Work> queue, StateMachine machine, MachineState state,
			Role role) {

		for (Move m : moves) {
			Work w = new Work();
			FirstMove f = new FirstMove();
			f.m = m;
			f.alpha = MIN_SCORE;
			f.beta = MAX_SCORE;
			w.original = f;
			w.m = m;
			w.max = false;
			w.state = state;
			queue.add(w);
		}

		int terminals = 0;
		while (queue.size() < N_THREADS * N_EXPAND && queue.size() > terminals) {
			Work w = queue.poll();
			try {
				if (w.max) {
					Set<Work> expand = new HashSet<Work>();
					terminals += maxscore(w, machine, role, expand);
					queue.addAll(expand);
				}
				else {
					Set<Work> expand = new HashSet<Work>();
					minscore(w, machine, role, expand);
					queue.addAll(expand);
				}
			} catch (GoalDefinitionException | MoveDefinitionException | TransitionDefinitionException e) {
				e.printStackTrace();
			}
		}
	}

	private int maxscore(Work work, StateMachine machine, Role role, Set<Work> expand)
			throws GoalDefinitionException,
			MoveDefinitionException, TransitionDefinitionException {
		if (machine.isTerminal(work.state)) {
			expand.add(work);
			return 1;
		}
		List<Move> actions = machine.findLegals(role, work.state);
		for (Move move : actions) {
			Work w = new Work();
			w.original = work.original;
			w.m = move;
			w.max = false;
			w.state = work.state;
			expand.add(w);
		}
		return 0;
	}

	// as seen in notes ch 6
	private void minscore(Work work, StateMachine machine, Role role, Set<Work> expand)
			throws GoalDefinitionException,
			MoveDefinitionException, TransitionDefinitionException {
		// use joint moves so that we can deal with n-player games; n != 2
		for (List<Move> jmove : machine.getLegalJointMoves(work.state, role, work.m)) {
			MachineState next = machine.getNextState(work.state, jmove);
			Work w = new Work();
			w.original = work.original;
			w.m = null;
			w.max = true;
			w.state = next;
			expand.add(w);
		}
	}

	private void joinAll(Set<Thread> threads) {
		for (Thread t : threads) {
			try {
				t.join();
			} catch (InterruptedException e) {
				return;
			}
		}
	}

	@Override
	public void stateMachineStop() {
		return;
	}

	@Override
	public void stateMachineAbort() {
		return;
	}

	@Override
	public void preview(Game g, long timeout) throws GamePreviewException {
		return;
	}

	@Override
	public ConfigPanel getConfigPanel() {
		return new Config(new GridLayout(N_OPTIONS, 1), this);
	}

	@Override
	public String getName() {
		return "Brian and Jeff'); DROP TABLE TEAMS; --";
	}

}
