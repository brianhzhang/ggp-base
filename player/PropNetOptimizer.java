import org.ggp.base.util.Pair;
import org.ggp.base.util.gdl.grammar.GdlConstant;
import org.ggp.base.util.gdl.grammar.GdlPool;
import org.ggp.base.util.propnet.architecture.Component;
import org.ggp.base.util.propnet.architecture.PropNet;
import org.ggp.base.util.propnet.architecture.components.*;
import org.ggp.base.util.statemachine.Role;

import java.util.*;

public class PropNetOptimizer {

	PropNet p;

	public PropNetOptimizer(PropNet p) {
		this.p = p;
	}

	private Component trueComponent = null;

	private int condenseDuplicates(Component c, List<Component> possibles) {
		for (Component poss : possibles) {
			if (!c.getClass().equals(poss.getClass())) continue;
			for (Component next : c.getOutputs()) {
				poss.addOutput(next);
				next.addInput(poss);
			}
			int out = c.getInputs().size() + c.getOutputs().size();
			p.removeComponent(c);
			return out;
		}
		// failed
		possibles.add(c);
		return 0;
	}

	private void findComponentsBackwards(Component current, Set<Component> visited) {
		Queue<Component> queue = new LinkedList<>();
		queue.add(current);
		while (!queue.isEmpty()) {
			current = queue.poll();
			if (visited.contains(current)) continue;
			visited.add(current);
			for (Component parent : current.getInputs()) {
				queue.offer(parent);
			}
		}
	}

	private int trimInvalidDoes(Map<String, Integer> inSizeMap) {
		int ntrimmed = 0;
		for (String doeslegal : Arrays.asList("does", "legal")) {
			for (Component c : new HashSet<>(p.getComponents())) {
				if (!(c instanceof Proposition)) continue;
				Proposition pin = (Proposition) c;
				if (!pin.getName().getName().toString().equals(doeslegal)) continue;
				if (inSizeMap.containsKey(pin.getName().get(0).toString())) continue;
				// role does not exist
				ntrimmed += c.getInputs().size() + c.getOutputs().size();
				p.removeComponent(c);
			}
		}
		return ntrimmed;
	}

	// (X or Y) and (X or Y or Z) ==> X or Y
	// (X and Y) or (X and Y and Z) ==> X and Y
	private int removeRedundantAndOr() {
		int count = 0;
		for (Component c : p.getComponents()) {
			List<Pair<Class<?>, Class<?>>> classList = Arrays.asList(
					Pair.of(And.class, Or.class),
					Pair.of(Or.class, And.class));
			for (Pair<Class<?>, Class<?>> f : classList) {
				// convention here: left = or, right = and
				if (!f.left.isInstance(c)) continue;
				List<Set<Component>> andInputSets = new ArrayList<>();
				List<Component> cinputs = new ArrayList<>(c.getInputs());
				Collections.sort(cinputs,
						Comparator.comparingInt(x -> x.getInputs().size()));
				for (Component in : cinputs) {
					if (!f.right.isInstance(in)) continue;
					boolean isSubset = false;
					for (Set<Component> inputSet : andInputSets) {
						if (isSubset(inputSet, in.getInputs())) {
							count += 1;
							c.removeInput(in);
							in.removeOutput(c);
							isSubset = true;
							break;
						}
					}
					if (!isSubset) andInputSets.add(in.getInputs());
				}
			}
		}
		return count;
	}

	// x and (~x or y) => x and y
	// x or (~x and y) => x or y
	private int removeContradictions() {

		Map<Class<?>, Map<Set<Component>, Component>> extant = new HashMap<>();
		extant.put(And.class, new HashMap<>());
		extant.put(Or.class, new HashMap<>());

		for (Component c : p.getComponents()) {
			if (!extant.containsKey(c.getClass())) continue;
			extant.get(c.getClass()).put(new HashSet<>(c.getInputs()), c);
		}

		int ntrimmed = 0;
		for (Component c : new HashSet<>(p.getComponents())) {
			List<Pair<Class<?>, Class<?>>> classList = Arrays.asList(
					Pair.of(And.class, Or.class),
					Pair.of(Or.class, And.class));
			for (Pair<Class<?>, Class<?>> f : classList) {
				// convention here: left = or, right = and
				if (!f.left.isInstance(c)) continue;
				Map<Component, Boolean> inputs = new HashMap<>();
				removeContradictionsInputFindingHelper(
						inputs, c, f.left, f.right, true);
				for (Component and : new HashSet<>(c.getInputs())) {
					if (!f.right.isInstance(and)) continue;
					boolean trimThisAnd = false;
					Set<Component> toKeep = new HashSet<>();
					for (Component input : and.getInputs()) {
						Component posInput = input;
						boolean value = true;
						while (posInput instanceof Not) {
							value = !value;
							posInput = posInput.getSingleInput();
						}
						if (inputs.containsKey(posInput)) {
							if (inputs.get(posInput) == value) {
								trimThisAnd = true;
								break;
							}
						} else {
							toKeep.add(input);
						}
					}

					if (trimThisAnd) {
						and.removeOutput(c);
						c.removeInput(and);
						ntrimmed++;
					} else {
						Map<Set<Component>, Component> extantAnd = extant.get(f.right);
						/*
						kind of jank; only optimizes out if there is a perfect
						other component to switch into. this way the number of edges
						cannot possibly go up.
						 */
						if (!toKeep.equals(and.getInputs())
								&& extantAnd.containsKey(toKeep)) {
							Component keep = extantAnd.get(toKeep);
							if (toKeep.equals(keep.getInputs())) {
								and.removeOutput(c);
								c.removeInput(and);
								keep.addOutput(c);
								c.addInput(keep);
								ntrimmed++;
							}
						}
					}
				}
			}
		}
		return ntrimmed;
	}

	private void removeContradictionsInputFindingHelper(
			Map<Component, Boolean> inputs, Component c,
			Class<?> or, Class<?> and, boolean flip) {
		if (!or.isInstance(c)) {
			inputs.put(c, flip);
			return;
		}
		for (Component input : c.getInputs()) {
			if (input instanceof Not) {
				removeContradictionsInputFindingHelper(
						inputs, input.getSingleInput(), and, or, !flip);
			} else {
				removeContradictionsInputFindingHelper(
						inputs, input, or, and, flip);
			}
		}
	}

	private <T> boolean isSubset(Set<T> inner, Set<T> outer) {
		for (T first : inner) {
			if (!outer.contains(first)) return false;
		}
		return true;
	}

	// (x and y1) or (x and y2) => x or (y1 and y2)
	private int factorAndOr()
			throws InstantiationException, IllegalAccessException {
		int ntrimmed = 0;
		for (Component c : new HashSet<>(p.getComponents())) {
			List<Pair<Class<?>, Class<?>>> classList = Arrays.asList(
					Pair.of(And.class, Or.class),
					Pair.of(Or.class, And.class));
			for (Pair<Class<?>, Class<?>> f : classList) {
				// convention here: left = or, right = and
				if (!f.left.isInstance(c)) continue;
				Component bestFactor = null;
				int bestCount = 1;
				Map<Component, List<Component>> ands = new HashMap<>();
				for (Component in : c.getInputs()) {
					if (!f.right.isInstance(in)) continue;
					for (Component in2 : in.getInputs()) {
						if (!ands.containsKey(in2)) ands.put(in2, new ArrayList<>());
						ands.get(in2).add(in);
						if (ands.get(in2).size() > bestCount) {
							bestFactor = in2;
							bestCount = ands.get(in2).size();
						}
					}
				}
				if (bestFactor == null) continue;
				List<Component> bestInput = ands.get(bestFactor);

				int delta = 4;
				for (Component in : bestInput) {
					delta += in.getInputs().size();
					if (in.getOutputs().size() == 1) {
						delta -= in.getInputs().size() + 1;
					}
				}
				if (delta >= 0) break;
				ntrimmed -= delta;

				// remove old links

				Component and = null;
				try {
					and = (Component) f.right.getDeclaredConstructor().newInstance();
				} catch (Exception e) {
					e.printStackTrace();
				}
				p.addComponent(and);
				and.addOutput(c);
				c.addInput(and);
				and.addInput(bestFactor);
				bestFactor.addOutput(and);

				Component or = null;
				try {
					or = (Component) f.left.getDeclaredConstructor().newInstance();
				} catch (Exception e) {
					e.printStackTrace();
				}
				p.addComponent(or);
				or.addOutput(and);
				and.addInput(or);

				for (Component in : bestInput) {
					in.removeOutput(c);
					c.removeInput(in);
					Component newAnd = new And();
					p.addComponent(newAnd);
					for (Component old : in.getInputs()) {
						if (old == bestFactor) continue;
						newAnd.addInput(old);
						old.addOutput(newAnd);
					}
					newAnd.addOutput(or);
					or.addInput(newAnd);
				}
			}
		}
		return ntrimmed;
	}

	private int condenseDoubles(Map<String, Integer> inSizeMap) {
		int ntrimmed = 0;
		List<Class<?>> classList = Arrays.asList(Or.class, And.class);
		for (Class<?> cls : classList) {
			Set<Component> removable = new HashSet<>();
			// global property of AND or OR
			Set<Component> candidates = new HashSet<>();
			for (Component c : p.getComponents()) {
				if (!cls.isInstance(c)) continue;
				for (Component prev : c.getInputs()) {
					if (!cls.isInstance(prev)) continue;
					candidates.add(c);
					break;
				}
			}
			Map<Component, Integer> outputCount = new HashMap<>();
			int delta = 0;
			for (Component c : candidates) {
				Set<Component> newInputs = new HashSet<>(c.getInputs());
				for (Component prev : c.getInputs()) {
					if (!cls.isInstance(prev)) continue;
					if (candidates.contains(prev)) continue;
					newInputs.addAll(prev.getInputs());
					delta -= 1;
					outputCount.put(prev, outputCount.getOrDefault(prev, 0) + 1);
					if (prev.getOutputs().size() == outputCount.get(prev)) {
						delta -= prev.getInputs().size();
						removable.add(prev);
					}
				}
				delta += newInputs.size() - c.getInputs().size();
				if (cls.equals(And.class)) continue;
				Map<String, Set<Component>> inMap = createInputMap(newInputs);
				for (Role role : p.getRoles()) {
					int sz = inMap.get(role.toString()).size();
					int delta2 = (inSizeMap.get(role.toString()) - sz) + 2 - sz;
					if (delta2 >= 0) continue;
					delta += delta2;
				}
			}

			if (delta >= 0) continue;
			ntrimmed -= delta;
			for (Component c : new HashSet<>(p.getComponents())) {
				if (!cls.isInstance(c)) continue;
				for (Component prev : new ArrayList<>(c.getInputs())) {
					if (!cls.isInstance(prev)) continue;
					if (candidates.contains(prev)) continue;
					for (Component pp : prev.getInputs()) {
						pp.addOutput(c);
						c.addInput(pp);
					}
					prev.removeOutput(c);
					c.removeInput(prev);
				}
			}
			for (Component c : removable) {
				assert c.getOutputs().isEmpty();
				ntrimmed += c.getInputs().size();
				p.removeComponent(c);
			}
		}
		for (Component c : new HashSet<>(p.getComponents())) {
			if (c instanceof Not) {
				if (c.getInputs().size() != 1) {
					System.out.println(c + " " + c.getInputs());
				}
				Component prev = c.getSingleInput();
				if (!(prev instanceof Not)) continue;
				Component pp = prev.getSingleInput();
				for (Component out : c.getOutputs()) {
					pp.addOutput(out);
					out.addInput(pp);
				}
				ntrimmed += c.getInputs().size() + c.getOutputs().size();
				p.removeComponent(c);
			}
		}
		return ntrimmed;
	}

//	private  String getName(Component comp) {
//		String toParse = comp.toString();
//		int start = toParse.indexOf("label=\"") + 7;
//		int end = toParse.indexOf("\"", start);
//		return toParse.substring(start, end);
//	}

	private Map<String, Set<Component>> createInputMap(Set<Component> inputs) {
		Map<String, Set<Component>> inMap = new HashMap<>();
		for (Role role : p.getRoles()) {
			inMap.put(role.toString(), new HashSet<>());
		}
		for (Component in : inputs) {
			if (!(in instanceof Proposition)) continue;
			Proposition pin = (Proposition) in;
			if (!pin.getName().getName().toString().equals("does")) continue;
			inMap.get(pin.getName().get(0).toString()).add(in);
		}
		return inMap;
	}

	private int simplifyOrDoes(Map<String, Integer> inSizeMap) {
		int ntrimmed = 0;
		for (Component c : new HashSet<>(p.getComponents())) {
			if (!(c instanceof Or)) continue;
			Map<String, Set<Component>> inMap = createInputMap(c.getInputs());
			for (Role role : p.getRoles()) {
				int sz = inMap.get(role.toString()).size();
				int delta = (inSizeMap.get(role.toString()) - sz) + 2 - sz;
				if (delta >= 0) continue;
				ntrimmed -= delta;
				// can reduce!
				// 1. make the new NOT/OR gate
				Not topnot = new Not();
				p.addComponent(topnot);
				topnot.addOutput(c);
				c.addInput(topnot);
				Or or = new Or();
				p.addComponent(or);
				or.addOutput(topnot);
				topnot.addInput(or);

				for (Component in : inMap.get(role.toString())) {
					// 2. remove existing links
					in.removeOutput(c);
					c.removeInput(in);
				}
				for (Proposition legal : p.getLegalPropositions().get(role)) {
					Proposition does = p.getLegalInputMap().get(legal);
					if (inMap.get(role.toString()).contains(does)) continue;
					does.addOutput(or);
					or.addInput(does);
				}
			}
		}
		return ntrimmed;
	}

	private Set<Component> getCritical(boolean includeBaseInit) {
		Set<Component> critical = new HashSet<>();
		// critical: terminal, input, goal, legal
		if (p.getTerminalProposition() == null) {
			Log.println("error: no terminal proposition. something bad happened");
		}
		critical.add(p.getTerminalProposition());
		critical.addAll(p.getInputPropositions().values());
		for (Role role : p.getRoles()) {
			critical.addAll(p.getGoalPropositions().get(role));
			critical.addAll(p.getLegalPropositions().get(role));
		}
		if (includeBaseInit) {
			critical.addAll(p.getBasePropositions().values());
			if (p.getInitProposition() != null) critical.add(p.getInitProposition());
		}
		return critical;
	}

	private int removeUnreachable(Set<Component> critical) {

		Set<Component> important = new HashSet<>();
		for (Component comp : critical) {
			findComponentsBackwards(comp, important);
		}
		Set<Component> unimportant = new HashSet<>(p.getComponents());
		unimportant.removeAll(important);
		int ntrimmed = 0;
		for (Component c : unimportant) {
			ntrimmed += c.getInputs().size() + c.getOutputs().size();
			p.removeComponent(c);
		}
		return ntrimmed;
	}

	// all DOES with no corresponding LEGAL are hardwired to FALSE.
	private int removeDoesWithoutLegal() {
		int ntrimmed = 0;
		for (Component c : new ArrayList<>(p.getComponents())) {
			if (!(c instanceof Proposition)) continue;
			Proposition prop = (Proposition) c;
			GdlConstant type = prop.getName().getName();
			if (type == GdlPool.DOES) {
				if (!p.getLegalInputMap().containsKey(prop)) {
//					Log.println("removing useless action " + prop.getName());
					ntrimmed += hardwire(prop, false);
				}
			}
		}
		return ntrimmed;
	}

	// ONLY SHOULD BE USED ON DOES COMPONENTS
	// NEEDS TO CONSIDER CRITICAL COMPONENTS TO WORK ON COMPONENTS EARLIER IN TREE
	private int hardwire(Component c, boolean value) {
		int ntrimmed = 0;
		for (Component next : new HashSet<>(c.getOutputs())) {
			ntrimmed += hardwire(c, next, false);
		}
		p.removeComponent(c);
		return ntrimmed;
	}

	private int hardwire(Component comp, Component next, boolean value) {
		int ntrimmed = 0;
		comp.removeOutput(next);
		next.removeInput(comp);
		ntrimmed++;
		if (next instanceof Transition) {
			if (value) {
				getTrueComponent().addOutput(next);
				next.addInput(getTrueComponent());
				ntrimmed--;
			}
		} else if (next instanceof Not) {
			ntrimmed += hardwire(next, !value);
		} else if (next.getInputs().isEmpty()) {
			ntrimmed += hardwire(next, value);
		} else if ((next instanceof And && !value)
				|| (next instanceof Or && value)) {
			ntrimmed += hardwire(next, value);
		}
		return ntrimmed;
	}

	private int condenseIdentical(Set<Component> critical) {
		int ntrimmed = 0;
		Map<Set<Component>, List<Component>> inputMaps = new HashMap<>();
		for (Component c : new HashSet<>(p.getComponents())) {
			if (c instanceof Transition) continue;
			if (c instanceof Constant) continue;
			if (critical.contains(c)) continue;
			if (!inputMaps.containsKey(c.getInputs())) {
				inputMaps.put(c.getInputs(), new ArrayList<>());
			}
			List<Component> possibles = inputMaps.get(c.getInputs());
			ntrimmed += condenseDuplicates(c, possibles);
		}
		return ntrimmed;
	}

	private int removeSingleInput(Set<Component> critical) {
		int ntrimmed = 0;
		for (Component c : new HashSet<>(p.getComponents())) {
			if (c instanceof Not) continue;
			if (c instanceof Transition) continue;
			if (c instanceof Constant) continue;
			if (critical.contains(c)) continue;
			if (c.getInputs().size() != 1) continue;
			Component in = c.getSingleInput();
			for (Component out : c.getOutputs()) {
				in.addOutput(out);
				out.addInput(in);
			}
			p.removeComponent(c);
			ntrimmed++;
		}
		return ntrimmed;
	}

	private Component getTrueComponent() {
		if (trueComponent == null || !p.getComponents().contains(trueComponent)) {
			trueComponent = new Constant(true);
			p.addComponent(trueComponent);
		}
		return trueComponent;
	}

	public void optimizePropnet(boolean keepAllBases)
			throws InstantiationException, IllegalAccessException {
//		if (true) return;

		trueComponent = null;
		for (Component comp : p.getComponents()) {
			if (comp instanceof Constant && comp.getValue()) {
				trueComponent = comp;
				break;
			}
		}

//		if (true) return;

		List<Integer> changed = new ArrayList<>();

		for (int round = 1; ; round++) {

			Log.print("optimizing propnet: round " + round + " ");

			Map<String, Integer> inSizeMap = new HashMap<>();
			for (Role role : p.getRoles()) {
				String s = role.toString();
				inSizeMap.put(s, p.getLegalPropositions().get(role).size());
			}

			Set<Component> critical = getCritical(keepAllBases);
			Set<Component> criticalExtended = getCritical(true);

			// metrics of propnet size:
			/*
			1. number of edges
			2. sum(c.noutputs * c.ninputs for components c)
					[used by removeContradictions]
			 */

			List<Integer> order = new ArrayList<>(Arrays.asList(0, 1, 2, 3, 4, 5, 6, 7, 8, 9));
			List<Integer> print = new ArrayList<>(order);
			Collections.shuffle(order);

			for (int x : order) {

				if (x == 0) print.set(x, trimInvalidDoes(inSizeMap));
				// factorAndOr: requires removeUnreachable
				if (x == 1) print.set(x, factorAndOr());
				if (x == 2) print.set(x, removeRedundantAndOr());
				if (x == 3) print.set(x, removeContradictions());
				// condenseDoubles: requires simplifyOrDoes, removeUnreachable
				if (x == 4) print.set(x, condenseDoubles(inSizeMap));
				if (x == 5) print.set(x, simplifyOrDoes(inSizeMap));

				if (x == 6) print.set(x, removeUnreachable(critical));
				if (x == 7) print.set(x, removeDoesWithoutLegal());
				if (x == 8) print.set(x, condenseIdentical(criticalExtended));
				if (x == 9) print.set(x, removeSingleInput(criticalExtended));
			}
			// === removing single-input components
			// i.e. are anything that has one input (i.e. anon, view props)
			// exceptions: NOT, TRANSITION, CONSTANT, and non-view propositions.
			// add base, init to critical

			Log.println(print + " | remaining: " +
					Arrays.asList(p.getSize(),
							p.getNumLinks(),
							p.getBasePropositions().size()));

			if (print.equals(changed)) break;
			changed = print;
		}
		Log.println("verifying propnet consistency");
		checkConsistency();
		Log.println("propnet optimization complete");
	}

	private void checkConsistency() {
		for (Component c : p.getComponents()) {
			for (Component in : c.getInputs()) {
				assert p.getComponents().contains(in);
				assert in.getOutputs().contains(c);
			}
			for (Component out : c.getOutputs()) {
				assert p.getComponents().contains(out);
				assert out.getInputs().contains(c);
			}
		}
	}
}
