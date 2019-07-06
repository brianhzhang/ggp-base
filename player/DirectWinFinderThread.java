import org.ggp.base.util.gdl.grammar.GdlConstant;
import org.ggp.base.util.gdl.grammar.GdlPool;
import org.ggp.base.util.gdl.grammar.GdlSentence;
import org.ggp.base.util.propnet.architecture.Component;
import org.ggp.base.util.propnet.architecture.PropNet;
import org.ggp.base.util.propnet.architecture.components.*;
import org.ggp.base.util.statemachine.MachineState;
import org.ggp.base.util.statemachine.Role;

import java.util.*;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;



public class DirectWinFinderThread extends Thread {
	private JustKiddingPropNetStateMachine oldm;
	private FuzzyStateMachine m;
	private int ourRoleIndex;
	private double ourWeight;
	private boolean[] friends;
	private boolean[] reverseFriends;

	private Set<MachineState> visited;

	public BlockingQueue<Stack<? extends StateContainer>> input;
	public BlockingQueue<Output> output;

	public boolean kill = false;
	public boolean finalKill = false;

	public boolean debug = false;
	private int nodesSearched = 0;
	private int nodesSolved = 0;
	private int nodesSkipped = 0;

	class Output {
		public MachineState input;
		public double lower;
		public double upper;
	}

	static final int MAX_DEPTH = 16;

	public interface StateContainer {
		public MachineState getState();
	}

	public void assertReady() {
		assert input.isEmpty();
		assert output.isEmpty();
		assert !kill;
	}

	public DirectWinFinderThread(JustKiddingPropNetStateMachine machine,
			int ourRoleIndex, double ourWeight) {
		// this constructor should not use the machine at all
		this.oldm = machine;
		this.ourRoleIndex = ourRoleIndex;
		this.ourWeight = ourWeight;
		this.input = new LinkedBlockingQueue<>();
		this.output = new LinkedBlockingQueue<>();
		this.visited = new HashSet<>();

		this.friends = new boolean[machine.getRoles().size()];
		this.reverseFriends = new boolean[machine.getRoles().size()];
	}

	public void run() {
		try {
			run_();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	public void setFriends(boolean[] friends) {
		this.friends = friends;
		for (int i = 0; i < friends.length; i++) {
			this.reverseFriends[i] = !this.friends[i];
		}
	}

	public double findBounds(MachineState state, boolean[] friends) {
		m.friends = friends;
		m.setState(state);
		m.routes = null;
		int[] root = m.getBase();

		long start = System.currentTimeMillis();

		List<List<Set<Integer>>> candidates = new ArrayList<>();

		for (int d = 0; d < MAX_DEPTH; d++) {
			if (!candidates.isEmpty()) break;

//			System.out.println("starting depth = " + d);
			int[] nextState = m.getNextState(null);
			if (kill) return 100;
//			System.out.println("state found");
			m.setState(nextState);
//			System.out.println("state switched");
//			m.prettyState();

//			m.printComponent("goal white 0");

			for (int r = 0; r < m.goalsByRole.length; r++) {
				if (!friends[r]) continue;
				int[] ourGoals = m.goalsByRole[r];
				for (int i = 0; i < ourGoals.length; i++) {
					int goalValue = m.comps[ourGoals[i]];
					if (goalValue == m.FRIEND || goalValue == m.OR) {
						if (m.propDetails[ourGoals[i]] == 100) {
							List<Set<Integer>> candidate = new ArrayList<>();


							Set<Integer> visited = new HashSet<>();
							m.findFriendsBackwards(ourGoals[i], visited);
//							System.out.println("compiling routestore");
							Set<RouteStore> visitedRoutes = new HashSet<>();
							for (int comp : visited) {
								if (m.propTypes[comp] == GdlPool.TRUE) {

									RouteStore store = m.routes[m.propDetails[comp]];
									List<Set<Integer>> compiled = store.compile(visitedRoutes);
									GdlSentence propName = ((Proposition) m.compList[comp]).getName();
									candidate = RouteStore.union(candidate, compiled);
								}
							}
//							System.out.println("done");
							candidates.add(candidate);
//							prettyCandidate(candidate);
						}
					}
				}
			}
		}


		double bound = 0;

//		System.out.println("doing search");

		for (List<Set<Integer>> candidate : candidates) {
			DoSearchReturn ret = doSearch(friends, candidate, 0, root, 0, 100);
			if (ret != null) {
				bound = Math.max(bound, ret.value);
				if (bound == 100) break;
			}
		}
		return bound;
	}

	public void run_() throws InterruptedException {
		this.m = new FuzzyStateMachine(oldm, this);

		friends = new boolean[m.goalsByRole.length];
		friends[ourRoleIndex] = true;
		setFriends(friends);
//
//		try {
//			String contents = new String(Files.readAllBytes(Paths.get("state.txt")));
//			m.setStateFromString(contents);
//			m.setState(m.getBase().clone());
//			m.prettyState();
//			int[] base = m.getBase();
//			boolean[] baseBoolean = new boolean[base.length];
//			for (int i = 0; i < base.length; i++) {
//				baseBoolean[i] = base[i] == m.TRUE;
//			}
//			PropNetMachineState next = new PropNetMachineState(baseBoolean);
//
//			Output outputStruct = new Output();
//
//			outputStruct.input = next;
//			outputStruct.lower = findBounds(next, friends);
//			outputStruct.upper = 100 - findBounds(next, reverseFriends);
//			System.out.println(outputStruct.lower + " " + outputStruct.upper);
//		} catch (IOException e) {
//			e.printStackTrace();
//		}


		while (true) {

			if (finalKill) {
				Log.println("direct win finder: game over. terminating");
				return;
			}
			if (kill) {
				Log.printf("direct win finder: %d solved, %d skipped, %d searched, " +
						"%d unread\n",
						nodesSolved, nodesSkipped, nodesSearched, input.size());
				nodesSearched = 0;
				nodesSolved = 0;
				nodesSkipped = 0;
				input.clear();
				output.clear();
				visited.clear();
				kill = false;
			}


			Stack<? extends StateContainer> stack = input.poll();

			// busy waiting isn't great, but I don't expect this to happen much at all
			if (stack == null) {
				Thread.sleep(10);
				continue;
			}

			boolean alreadySolved = false;
			for (StateContainer state : stack) {
				if (visited.contains(state)) {
					alreadySolved = true;
					break;
				}
			}
			if (alreadySolved) {
				nodesSkipped++;
				continue;
			}

			MachineState next = ((StateContainer) stack.peek()).getState();

//			System.out.println(next);

			Output outputStruct = new Output();

			if (debug) {
				m.setState(next);
				m.prettyState();
			}
			outputStruct.input = next;
			outputStruct.lower = findBounds(next, friends);
			outputStruct.upper = 100 - findBounds(next, reverseFriends);

			if (kill) continue;


			if (outputStruct.lower > 0 || outputStruct.upper < 100) {
				assert outputStruct.lower <= outputStruct.upper;
				output.put(outputStruct);
				nodesSolved++;
			}

			if (outputStruct.lower == outputStruct.upper) {
				visited.add(next);
			}

			nodesSearched++;

		}
	}

	public DoSearchReturn doSearch(boolean[] friends,
			List<Set<Integer>> candidate,
			int depth, int[] state, double alpha, double beta) {
		if (kill) return null;

		int[] old = m.getBase();
		m.setState(state);
//		System.out.println("depth = " + depth);
//		m.prettyState();


		DoSearchReturn ret = doSearchHelper(
				friends, candidate, depth, state, alpha, beta);

		m.setState(old);
//		System.out.println(ret);
		return ret;
	}

	private DoSearchReturn doSearchHelper(boolean[] friends,
			List<Set<Integer>> candidate,
			int depth, int[] state, double alpha, double beta) {
		DoSearchReturn ret = new DoSearchReturn(alpha);
		double totalWeight = 0;
		double worstGoal = 0;
		boolean isTerminal = false;

		for (int r = 0; r < m.goalsByRole.length; r++) {
			double worstRoleGoal = friends[ourRoleIndex] ? 100 : 0;
			int[] ourGoals = m.goalsByRole[r];
			for (int i = 0; i < ourGoals.length; i++) {
				int goalComp = m.comps[ourGoals[i]];
				int goalValue = m.propDetails[ourGoals[i]];
				if (r != ourRoleIndex) goalValue = 100 - goalValue;
				if (goalComp == m.TRUE) {
					worstRoleGoal = goalValue;
					isTerminal = true;
					break;
				} else if (goalComp == m.ENEMY) {
					if (friends[ourRoleIndex]) {
						worstRoleGoal = Math.min(worstRoleGoal, goalValue);
					} else {
						worstRoleGoal = Math.max(worstRoleGoal, goalValue);
					}
				}
			}
//			System.out.println(worstRoleGoal);
			double weight = (r == ourRoleIndex) ? ourWeight : 1;
			worstGoal += worstRoleGoal * weight;
			totalWeight += weight;
		}
		worstGoal /= totalWeight;
		if (!friends[ourRoleIndex]) worstGoal = 100 - worstGoal;
//		System.out.println(worstGoal);

		if (isTerminal) {
			ret.value = Math.max(alpha, Math.min(beta, worstGoal));
//			System.out.println(ret.value + " " + worstGoal + " " + alpha + " " + beta + " " + goals);
			return ret;
		}

		if (worstGoal <= alpha) return ret;
		if (worstGoal < beta) beta = worstGoal;

		if (depth >= candidate.size()) return ret;

		List<Set<Integer>> legalMoves = new ArrayList<>();
		for (int r = 0; r < m.goalsByRole.length; r++) {
			if (!friends[r]) legalMoves.add(new HashSet(Arrays.asList(-1)));
			else {
				Set<Integer> roleLegal = m.findLegalMoves(r);
				if (roleLegal.size() > 1) roleLegal.retainAll(candidate.get(depth));
				if (roleLegal.size() == 0) return ret;
				legalMoves.add(roleLegal);
			}
		}

//		System.out.println(legalMoves);


		List<List<Integer>> legalJointMoves = new ArrayList<>();
		crossProduct(legalMoves, legalJointMoves, null);

		for (List<Integer> jointMove : legalJointMoves) {
			int[] newState = m.getNextState(jointMove);
			DoSearchReturn child = doSearch(friends, candidate, depth + 1,
					newState, alpha, beta);
			if (child == null) return null;
			if (child.value > alpha) {
				alpha = ret.value = child.value;
				ret.info = jointMove;
				ret.path = child;
				if (alpha == beta) break;
			}
		}


		return ret;
	}

	class DoSearchReturn {
		double value;
		Object info;
		DoSearchReturn path;

		public DoSearchReturn(double value) {
			this.value = value;
		}

		public String toString() {
			return value + " " + info + " -> " + path;
		}
	}

	private <T> void crossProduct(List<Set<T>> legals, List<List<T>> crossProduct,
			LinkedList<T> partial) {
		if (partial == null) partial = new LinkedList<>();
		if (partial.size() == legals.size()) {
			crossProduct.add(new ArrayList<T>(partial));
		} else {
			for (T move : legals.get(partial.size())) {
				partial.addLast(move);
				crossProduct(legals, crossProduct, partial);
				partial.removeLast();
			}
		}
	}

	public void prettyCandidate(List<? extends Collection<Integer>> candidate) {
		List<List<String>> gdls = new ArrayList<>();
		for (int i = 0; i < candidate.size(); i++) {
			gdls.add(new ArrayList<>());
			for (int comp : candidate.get(i)) {
				gdls.get(i).add(((Proposition) m.compList[comp]).getName().toString());
			}
		}
		System.out.println(gdls);
	}
}

class RouteStore {
	Set<Integer> does = new HashSet<>();
	List<RouteStore> prev = new ArrayList<>();

	public static List<Set<Integer>> union(
			List<Set<Integer>> one, List<Set<Integer>> two) {
		if (one == null) return two;
		if (two == null) return one;
		if (one.size() < two.size()) {
			List<Set<Integer>> tmp = two;
			two = one;
			one = tmp;
		}
		for (int i = 1; i <= two.size(); i++) {
			one.get(one.size() - i).addAll(two.get(two.size() - i));
		}
		return one;
	}

	public List<Set<Integer>> compile(Set<RouteStore> visited) {
		if (visited.contains(this)) return null;
		visited.add(this);
		List<Set<Integer>> output = new ArrayList<>();
		if (prev != null) {
			for (RouteStore pr : prev) {
				List<Set<Integer>> compiled = pr.compile(visited);
				output = union(output, compiled);
			}
		}
		output.add(does);
		return output;
	}
}

class FuzzyStateMachine {
	/*
	The four constants below decide the state of any particular component:
	FALSE and TRUE:	self-explanatory.
	CONTROLLED:
		means that Hero MAY have control of this component,
		and Villain DOES NOT have control of this component.
	ADVERSARIAL: Villain MAY have control of this component.
	 */
	static final int FALSE = 0;
	static final int FRIEND = 1;
	static final int ENEMY = 2;
	static final int OR = 3;
	static final int AND = 4;
	static final int TRUE = 5;

	static final Proposition NULL_PROP = new Proposition(null);

	JustKiddingPropNetStateMachine m;
	PropNet p;

	Role[] roles;
	int[] comps;
	int[] initcomps;
	Component[] compList;
	Map<Component, Integer> indexMap;
	int[][] forwardStructure;
	int[][] backwardStructure;
	int[] basearr;

	int[][] legalsByRole;
	int[][] goalsByRole;

	int[] currentState;

	boolean[] friends;

	GdlConstant[] propTypes;

	// @formatter:off
	static final int[][] T_AND = {
			/* FALSE  */ {FALSE,  FALSE, FALSE,  FALSE, FALSE,  FALSE},
			/* FRIEND */ {FALSE, FRIEND,   AND, FRIEND,   AND, FRIEND},
			/* ENEMY  */ {FALSE,    AND, ENEMY,  ENEMY,   AND,  ENEMY},
			/* OR     */ {FALSE, FRIEND, ENEMY,     OR,   AND,     OR},
			/* AND    */ {FALSE,    AND,   AND,    AND,   AND,    AND},
			/* TRUE   */ {FALSE, FRIEND, ENEMY,     OR,   AND,   TRUE},
	};
//
//	static final int[][] T_AND = {
//			/* FALSE  */ {FALSE,  FALSE, FALSE,  FALSE, FALSE,  FALSE},
//			/* FRIEND */ {FALSE, FRIEND,   AND,  ENEMY,   AND, FRIEND},
//			/* ENEMY  */ {FALSE,    AND, ENEMY,  ENEMY,   AND,  ENEMY},
//			/* OR     */ {FALSE,  ENEMY, ENEMY,  ENEMY, ENEMY,     OR},
//			/* AND    */ {FALSE,    AND,   AND,  ENEMY,   AND,    AND},
//			/* TRUE   */ {FALSE, FRIEND, ENEMY,     OR,   AND,   TRUE},
//	};
	// @formatter:on

	static final int[] T_NOT = {TRUE, FRIEND, ENEMY, AND, OR, FALSE};

	static final int[][] T_OR = getTableOr();


	// {FALSE, FRIEND, ENEMY, OR, AND, TRUE}
	static final int[][] DOES_VALUES = {
			T_AND[ENEMY], T_AND[FRIEND],
			};


	static int[][] getTableOr() {
		int N = 6;
		int[][] orTable = new int[N][N];
		for (int i = 0; i < N; i++) {
			for (int j = 0; j < N; j++) {
				orTable[i][j] = T_NOT[T_AND[T_NOT[i]][T_NOT[j]]];
			}
		}
		return orTable;
	}

	/*
	legal -> index of input
	input -> index of legal
	base -> index into basearr
	goal -> goal value
	 */
	int[] propDetails;
	/* legal, input, goal -> which role */
	int[] propRoles;


	// current search state
	RouteStore[] routes;

	DirectWinFinderThread mainThread;

	public static PropNet copyPropNet(PropNet p) {
		Map<Component, Component> newComponentMap = new HashMap<>();
		for (Component c : p.getComponents()) {
			Component copy = null;
			try {
				if (c instanceof Proposition) {
					GdlSentence name = ((Proposition) c).getName();
					copy = new Proposition(name);
					if (name.getName() == GdlPool.DOES) {
						if (!p.getLegalInputMap().containsKey(c)) {
							System.out.println("warning: legal and input do not match");
						}
					}
				} else if (c instanceof Constant) {
					copy = new Constant(((Constant) c).getValue());
				} else {
					copy = c.getClass().getDeclaredConstructor().newInstance();
				}
			} catch (Exception e) {
				e.printStackTrace();
			}
			newComponentMap.put(c, copy);
		}
		for (Component c : p.getComponents()) {
			for (Component output : c.getOutputs()) {
				Component newInput = newComponentMap.get(c);
				Component newOutput = newComponentMap.get(output);
				newInput.addOutput(newOutput);
				newOutput.addInput(newInput);
			}
		}
		return new PropNet(p.getRoles(), new HashSet<>(newComponentMap.values()));
	}

	private void addEdge(Component a, Component b) {
		a.addOutput(b);
		b.addInput(a);
	}

	private void removeEdge(Component a, Component b) {
		a.removeOutput(b);
		b.removeInput(a);
	}

	public FuzzyStateMachine(JustKiddingPropNetStateMachine machine,
			DirectWinFinderThread mainThread) {
		m = machine;
		p = copyPropNet(machine.p);
		this.mainThread = mainThread;

		Component terminal = p.getTerminalProposition();

		Component terminalInput = terminal.getSingleInput();
		removeEdge(terminalInput, terminal);

		Or newTerminalInput = new Or();
		p.addComponent(newTerminalInput);
		addEdge(newTerminalInput, terminal);

		// rewire goals
		for (Role role : p.getRoles()) {
			for (Proposition goal : p.getGoalPropositions().get(role)) {
				Component input = goal.getSingleInput();
				And and = new And();
				addEdge(input, and);
				addEdge(terminalInput, and);
				p.addComponent(and);

				removeEdge(input, goal);
				addEdge(and, goal);
				addEdge(goal, newTerminalInput);
			}
		}

		try {
			new PropNetOptimizer(p).optimizePropnet(true);
		} catch (Exception e) {
			e.printStackTrace();
		}

		compList = new Component[p.getSize()];
		comps = new int[p.getSize()];
		forwardStructure = new int[p.getSize()][];
		backwardStructure = new int[p.getSize()][];
		indexMap = new HashMap<Component, Integer>();
		basearr = new int[p.getBasePropositions().size()];
		friends = new boolean[p.getRoles().size()];

		roles = p.getRoles().toArray(n -> new Role[n]);
		propTypes = new GdlConstant[p.getSize()];
		propDetails = new int[p.getSize()];
		propRoles = new int[p.getSize()];


		{
			int i = 0;
			for (Component c : p.getComponents()) {
				compList[i] = c;
				comps[i] = FALSE;
				indexMap.put(c, i);
				i++;
			}
		}

		legalsByRole = new int[p.getRoles().size()][];
		goalsByRole = new int[p.getRoles().size()][];
		for (int i = 0; i < p.getRoles().size(); i++) {
			Role role = p.getRoles().get(i);

			Set<Proposition> legalMoves = p.getLegalPropositions().get(role);
			ArrayList<Proposition> legalMoveList = new ArrayList<>(legalMoves);
			legalsByRole[i] = new int[legalMoves.size()];
			for (int j = 0; j < legalMoves.size(); j++) {
				Proposition move = legalMoveList.get(j);
				legalsByRole[i][j] = indexMap.get(move);
			}

			Set<Proposition> goalSet = p.getGoalPropositions().get(role);
			List<Proposition> goals = new ArrayList<>(goalSet);
			Collections.sort(goals, Comparator.comparingInt(
					g -> Integer.parseInt(g.getName().get(1).toString())));
			goalsByRole[i] = new int[goals.size()];
			for (int j = 0; j < goals.size(); j++) {
				Proposition goal = goals.get(j);
				goalsByRole[i][j] = indexMap.get(goal);
			}
		}

		for (int i = 0; i < p.getBasePropositions().size(); i++) {
			Proposition origProp = ((Proposition) m.indexMapRev.get(m.basearr[i]));
			GdlSentence name = origProp.getName();
			Proposition prop = p.getBasePropositions().get(name);
			if (prop != null) {
				int idx = indexMap.get(prop);
				basearr[i] = idx;
				propDetails[idx] = i;
			}
		}

		for (int i = 0; i < p.getSize(); i++) {
			Component c = compList[i];
			forwardStructure[i] = makeComponentIntArray(c.getOutputs());
			backwardStructure[i] = makeComponentIntArray(c.getInputs());
			if (c instanceof Proposition) {
				GdlSentence name = ((Proposition) c).getName();
				propTypes[i] = name.getName();
				if (propTypes[i] == GdlPool.DOES) {
					int legal = indexMap.get(p.getLegalInputMap().get(c));
					propDetails[i] = legal;
					propDetails[legal] = i;
					int role = p.getRoles().indexOf(new Role((GdlConstant) name.get(0)));
					propRoles[i] = role;
					propRoles[legal] = role;
				} else if (propTypes[i] == GdlPool.GOAL) {
					int role = p.getRoles().indexOf(new Role((GdlConstant) name.get(0)));
					propRoles[i] = role;
					propDetails[i] = Integer.parseInt(name.get(1).toString());
				}
			}
		}

		for (int i = 0; i < comps.length; i++) {
			Component c = compList[i];
			if (c instanceof Not || c instanceof Constant) {
				propagate(i, getValue(i));
			}
		}

		initcomps = comps.clone();
	}

	private int[] makeComponentIntArray(Set<Component> comps) {
		int[] output = new int[comps.size()];
		int i = 0;
		for (Component comp : comps) {
			output[i] = indexMap.get(comp);
			i++;
		}
		return output;
	}

	private boolean isFriendIsh(int comp) {
		return comp == FRIEND || comp == OR;
	}

	public void findFriendsBackwards(int start, Set<Integer> visited) {
		Queue<Integer> queue = new LinkedList<>();
		int current = start;
		queue.add(current);

		while (!queue.isEmpty()) {
			current = queue.poll();
			if (visited.contains(current)) continue;
			if (!isFriendIsh(comps[current])) continue;
			visited.add(current);
			// convenient that NONE < 0
			if (propTypes[current] == GdlPool.DOES) queue.offer(propDetails[current]);
			if (propTypes[current] != GdlPool.TRUE) {
				for (int next : backwardStructure[current]) queue.offer(next);
			}
		}
	}

	private void resetPropnet() {
		for (int i = 0; i < comps.length; i++) {
			comps[i] = initcomps[i];
		}
	}

	public void setState(MachineState state) {
		boolean[] base = ((PropNetMachineState) state).props;
		if (m.use_propnet_reset) {
			resetPropnet();
		}
		int[] intstate = new int[base.length];
		for (int i = 0; i < base.length; i++) {
			intstate[i] = base[i] ? TRUE : FALSE;
		}
		setState(intstate);
	}

	public void setState(int[] state) {
		if (currentState == state) return;
		currentState = state;
		if (m.use_propnet_reset) {
			resetPropnet();
		}
		for (int i = 0; i < state.length; i++) propagate(basearr[i], state[i]);
	}

	private void setAllMoves(int r) {
		int uniqueLegal = -1;
		for (int i = 0; i < legalsByRole[r].length; i++) {
			int legal = legalsByRole[r][i];
			if (comps[legal] != FALSE) {
				if (uniqueLegal == -1) uniqueLegal = legal;
				else uniqueLegal = -2;
			}
			int doesValue = DOES_VALUES[friends[r] ? 1 : 0][comps[legal]];
//			System.out.println(compList[legal] + " " + comps[legal] + " " + doesValue);
			propagate(propDetails[legal], doesValue);
		}
		if (uniqueLegal >= 0) propagate(propDetails[uniqueLegal], TRUE);
	}

	public void setLegalMoves(List<Integer> moves) {
		if (moves == null) {
			for (int r = 0; r < roles.length; r++) setAllMoves(r);
		} else {
			for (int r = 0; r < roles.length; r++) {
				if (moves.get(r) == -1) setAllMoves(r);
				else {
					for (int i = 0; i < legalsByRole[r].length; i++) {
						int does = propDetails[legalsByRole[r][i]];
						propagate(does, moves.get(r) == does ? TRUE : FALSE);
					}
				}
			}
		}
	}

	public Set<Integer> findLegalMoves(int role) {
		Set<Integer> legalMoves = new HashSet<>();
		for (int i = 0; i < legalsByRole[role].length; i++) {
			int legal = legalsByRole[role][i];
			if (comps[legal] == TRUE) {
				legalMoves.add(propDetails[legal]);
			}
		}
		return legalMoves;
	}

	public int[] getNextState(List<Integer> moves) {
		setLegalMoves(moves);
//		System.out.println("legal moves set");

		int[] result = new int[basearr.length];
		RouteStore[] newRoutes = new RouteStore[basearr.length];

		for (int i = 0; i < basearr.length; i++) {
			if (mainThread.kill) return null;
			int transition = backwardStructure[basearr[i]][0];
			result[i] = comps[transition];
			if (moves == null) {
				if (isFriendIsh(result[i])) {
					RouteStore store = new RouteStore();
					if (routes == null) store.prev = null;
					Set<Integer> visited = new HashSet<>();
					findFriendsBackwards(transition, visited);
					for (int source : visited) {
						if (propTypes[source] == GdlPool.TRUE) {
							if (store.prev != null && routes[propDetails[source]] != null) {
								store.prev.add(routes[propDetails[source]]);
							}
						} else if (propTypes[source] == GdlPool.DOES) {
							store.does.add(source);
						}
					}
					newRoutes[i] = store;
				} else {
					newRoutes[i] = null;
				}
			}
		}
		if (moves == null) routes = newRoutes;
		else routes = null;
		return result;
	}

	public int[] getBase() {
		return currentState;
	}

	private void propagate(int idx, int value) {
		if (comps[idx] == value) return;

		comps[idx] = value;
		if (compList[idx] instanceof Transition) return;
		for (int next : forwardStructure[idx]) {
			propagate(next, getValue(next));
		}
	}


	private int getValue(int i) {
		if (compList[i] instanceof Proposition
				|| compList[i] instanceof Transition) {
			return comps[backwardStructure[i][0]];
		} else if (compList[i] instanceof Not) {
			return T_NOT[comps[backwardStructure[i][0]]];
		} else if (compList[i] instanceof And) {
			int result = TRUE;
			for (int input : backwardStructure[i]) {
				result = T_AND[result][comps[input]];
			}
			return result;
		} else if (compList[i] instanceof Or) {
			int result = FALSE;
			for (int input : backwardStructure[i]) {
				result = T_OR[result][comps[input]];
			}
			return result;
		} else if (compList[i] instanceof Constant) {
			return compList[i].getValue() ? TRUE : FALSE;
		}
		Log.println("error: component with unknown type: " + compList[i]);
		return -1; // ERROR
	}

	/* only debugging functions below this line */

	public void prettyState() {
		// only pretty in Breakthrough; for debugging
		List<String> props = new ArrayList<>();
		Map<String, Component> bases = new HashMap<>();
		for (int baseidx : basearr) {
			Proposition base = (Proposition) compList[baseidx];
			bases.put(base.getName().toString(), base);
			props.add(base.getName().toString());
		}
		Collections.sort(props);

//		{
//			int i = 0;
//			for (String s : props) {
//				if (i % 2 == 0) System.out.print(" ");
//				if (i % 16 == 0) System.out.println();
//				System.out.print(comps[indexMap.get(bases.get(s))]);
//				i++;
//			}
//		}

		System.out.println();

//		for (String s : props) {
//			int idx = indexMap.get(bases.get(s));
//			if (routes != null) {
//				assert (comps[idx] == FRIEND) == (routes[propDetails[idx]] != null);
//				if (comps[idx] == FRIEND) {
//					System.out.println(s + " " + routes[propDetails[idx]].does);
//				}
//			}
//		}

		for (int r = 0; r < goalsByRole.length; r++) {
			for (int i = 0; i < goalsByRole[r].length; i++) {
				int idx = goalsByRole[r][i];
				Proposition goal = (Proposition) compList[idx];
				System.out.println(goal.getName() + " " + idx + " " + comps[idx]);
			}
		}
	}

	private String getLabel(Component comp) {
		String st = comp.toString();
		st = st.substring(st.indexOf("label=\"") + "label=\"".length());
		st = st.substring(0, st.indexOf('"'));
		return st;
	}

	public void printStack(int comp, String indent) {
		String hash = Integer.toString(compList[comp].hashCode(), 16);
		System.out.println(indent + comps[comp] +
				" " + "00000000".substring(hash.length()) + hash +
				" " + getLabel(compList[comp]) + " " + compList[comp].getOutputs().size());
		if (propTypes[comp] == GdlPool.TRUE) return;
		for (int prev : backwardStructure[comp]) {
			printStack(prev, indent + "    ");
		}
	}

	public int[] setStateFromString(String s) {
		s = s.replaceAll("\\s", "");
//		System.out.println(s.length());
//		System.out.println(basearr.length);
		// only works in Breakthrough; for debugging
		List<String> props = new ArrayList<>();
		Map<String, Component> bases = new HashMap<>();
		for (int baseidx : basearr) {
			Proposition base = (Proposition) compList[baseidx];
			bases.put(base.getName().toString(), base);
			props.add(base.getName().toString());
		}
		Collections.sort(props);

		int[] state = new int[basearr.length];
		for (int i = 0; i < basearr.length; i++) {
			int idx = indexMap.get(bases.get(props.get(i)));
			int value = s.charAt(i) - '0';
			propagate(idx, value);
			state[this.propDetails[idx]] = value;
		}
		currentState = state;
		return getBase();
	}


	public void printComponent(String target) {
		for (Component comp : compList) {
			if (!(comp instanceof Proposition)) continue;
			Proposition prop = (Proposition) comp;
			if (!prop.getName().toString().contains(target)) continue;
			printStack(indexMap.get(prop.getSingleInput()), "");
		}
	}
}