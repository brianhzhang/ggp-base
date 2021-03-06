import org.ggp.base.player.gamer.exception.GamePreviewException;
import org.ggp.base.player.gamer.statemachine.StateMachineGamer;
import org.ggp.base.util.game.Game;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.StateMachine;
import org.ggp.base.util.statemachine.exceptions.GoalDefinitionException;
import org.ggp.base.util.statemachine.exceptions.MoveDefinitionException;
import org.ggp.base.util.statemachine.exceptions.TransitionDefinitionException;

public class SpeedTester extends StateMachineGamer {

	private class TestThread extends Thread {
		boolean stop;
		StateMachine m;
		int ncharges;
		int nsteps;
		boolean internal;
		long goals;

		public TestThread(StateMachine m, boolean internal) {
			this.m = m;
			stop = false;
			ncharges = 0;
			nsteps = 0;
			this.internal = internal;
		}

		@Override
		public void run() {
			MachineState init = m.getInitialState();
			if (!internal) {
				while (!stop) {
					MachineState state = init;
					while (!m.isTerminal(state)) {
						try {
							state = m.getRandomNextState(state);
						} catch (MoveDefinitionException | TransitionDefinitionException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
						nsteps++;
					}
					for (int i = 0; i < m.getRoles().size(); i++) {
						try {
							goals += m.getGoal(state, m.getRoles().get(i));
						} catch (GoalDefinitionException e) {
							e.printStackTrace();
						}
					}
					ncharges++;
				}
			} else {
				if (m instanceof JustKiddingPropNetStateMachine) {
					while (!stop) {
						MachineState state = init;
						int[] g = ((JustKiddingPropNetStateMachine) m)
								.internalDC((PropNetMachineState) state);
						for (int i = 0; i < g.length; i++) {
							goals += g[i];
						}
						ncharges++;
					}
				} else if (m instanceof YeahWasntTheLastOnePropNetStateMachine) {
					while (!stop) {
						MachineState state = init;
						int[] g = ((YeahWasntTheLastOnePropNetStateMachine) m)
								.internalDC((PropNetMachineState) state);
						for (int i = 0; i < g.length; i++) {
							goals += g[i];
						}
						ncharges++;
					}
				}
			}
			System.out.println("Done!");
		}

		public void halt() {
			stop = true;
		}

		public int getNum() {
			return ncharges;
		}

		public int getSteps() {
			return nsteps;
		}

		public long goals() {
			return goals;
		}
	}

	@Override
	public StateMachine getInitialStateMachine() {
		return new GDLGetter();
	}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		// BetterMetaPropNetStateMachineFactory m =
		// new BetterMetaPropNetStateMachineFactory(((GDLGetter)
		// getStateMachine()).getDescription());
		// LolAnotherMetaPropNetStateMachineFactory l =
		// new LolAnotherMetaPropNetStateMachineFactory(((GDLGetter)
		// getStateMachine()).getDescription());
		Log.setFile(getMatch().getMatchId() + "_" + getRole());
		Log.println("");
		StateMachine m1 = new JustKiddingPropNetStateMachine();
		StateMachine m2 = new YeahWasntTheLastOnePropNetStateMachine();
		m1.initialize(((GDLGetter) getStateMachine()).getDescription());
		m2.initialize(((GDLGetter) getStateMachine()).getDescription());
		TestThread t1 = new TestThread(m1, true);
		TestThread t2 = new TestThread(m2, true);
		t1.start();
		t2.start();
		long start = System.currentTimeMillis();
		while (System.currentTimeMillis() < timeout - 3000) {
			try {
				Thread.sleep(100);
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
		t1.halt();
		t2.halt();
		try {
			t1.join();
			t2.join();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		System.out.println("Seconds elapsed: " + 1.0 * (System.currentTimeMillis() - start) / 1000);
		System.out.println("Machine 1 depth charges: " + t1.getNum());
		System.out.println("Average Step Counter: " + (1.0 * t1.getSteps() / t1.getNum()));
		System.out.println("Average Aggregate Goals: " + (1.0 * t1.goals() / t1.getNum()));
		System.out.println("Machine 2 depth charges: " + t2.getNum());
		System.out.println("Average Step Counter: " + (1.0 * t2.getSteps() / t2.getNum()));
		System.out.println("Average Aggregate Goals: " + (1.0 * t2.goals() / t2.getNum()));
	}

	@Override
	public Move stateMachineSelectMove(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException {
		return null;
	}

	@Override
	public void stateMachineStop() {

	}

	@Override
	public void stateMachineAbort() {

	}

	@Override
	public void preview(Game g, long timeout) throws GamePreviewException {
		// TODO Auto-generated method stub

	}

	@Override
	public String getName() {
		return "Speed Test";
	}

}
