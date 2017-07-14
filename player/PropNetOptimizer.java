import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import org.ggp.base.util.Pair;
import org.ggp.base.util.propnet.architecture.Component;
import org.ggp.base.util.propnet.architecture.PropNet;
import org.ggp.base.util.propnet.architecture.components.And;
import org.ggp.base.util.propnet.architecture.components.Constant;
import org.ggp.base.util.propnet.architecture.components.Not;
import org.ggp.base.util.propnet.architecture.components.Or;
import org.ggp.base.util.propnet.architecture.components.Proposition;
import org.ggp.base.util.propnet.architecture.components.Transition;
import org.ggp.base.util.statemachine.Role;

public class PropNetOptimizer {

	private static int condenseDuplicates(PropNet p, Component c, List<Component> possibles) {
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

	private static void findComponentsBackwards(Component current, Set<Component> visited) {
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

	private static int trimInvalidDoes(PropNet p, Map<String, Integer> inSizeMap) {
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

	private static int factorAndOr(PropNet p)
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

				Component and = (Component) f.right.newInstance();
				p.addComponent(and);
				and.addOutput(c);
				c.addInput(and);
				and.addInput(bestFactor);
				bestFactor.addOutput(and);

				Component or = (Component) f.left.newInstance();
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

	private static int condenseDoubles(PropNet p, Map<String, Integer> inSizeMap) {
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
				Map<String, Set<Component>> inMap = createInputMap(p, newInputs);
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

//	private static String getName(Component comp) {
//		String toParse = comp.toString();
//		int start = toParse.indexOf("label=\"") + 7;
//		int end = toParse.indexOf("\"", start);
//		return toParse.substring(start, end);
//	}

	private static Map<String, Set<Component>> createInputMap(PropNet p, Set<Component> inputs) {
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

	private static int simplifyOrDoes(PropNet p, Map<String, Integer> inSizeMap) {
		int ntrimmed = 0;
		for (Component c : new HashSet<>(p.getComponents())) {
			if (!(c instanceof Or)) continue;
			Map<String, Set<Component>> inMap = createInputMap(p, c.getInputs());
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

	private static Set<Component> getCritical(PropNet p, boolean includeBaseInit) {
		Set<Component> critical = new HashSet<>();
		// critical: terminal, input, goal, legal
		critical.add(p.getTerminalProposition());
		critical.addAll(p.getInputPropositions().values());
		for (Role role : p.getRoles()) {
			critical.addAll(p.getGoalPropositions().get(role));
			critical.addAll(p.getLegalPropositions().get(role));
		}
		if (includeBaseInit) {
			critical.addAll(p.getBasePropositions().values());
			critical.add(p.getInitProposition());
		}
		return critical;
	}

	private static int removeUnreachable(PropNet p, Set<Component> critical) {

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

	private static int condenseIdentical(PropNet p, Set<Component> critical) {
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
			ntrimmed += condenseDuplicates(p, c, possibles);
		}
		return ntrimmed;
	}

	private static int removeSingleInput(PropNet p, Set<Component> critical) {
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

	public static void optimizePropnet(PropNet p)
			throws InstantiationException, IllegalAccessException {

		for (int round = 1;; round++) {
			List<Integer> print = new ArrayList<>();
			Log.print("optimizing propnet: round " + round + " ");

			Map<String, Integer> inSizeMap = new HashMap<>();
			for (Role role : p.getRoles()) {
				String s = role.toString();
				inSizeMap.put(s, p.getLegalPropositions().get(role).size());
			}

			Set<Component> critical = getCritical(p, false);
			Set<Component> criticalExtended = getCritical(p, true);

			print.add(trimInvalidDoes(p, inSizeMap));
			// factorAndOr: requires removeUnreachable
			print.add(factorAndOr(p));
			// condenseDoubles: requires simplifyOrDoes, removeUnreachable
			print.add(condenseDoubles(p, inSizeMap));
			print.add(simplifyOrDoes(p, inSizeMap));
			print.add(removeUnreachable(p, critical));
			print.add(condenseIdentical(p, criticalExtended));
			print.add(removeSingleInput(p, criticalExtended));

			// === removing single-input components
			// i.e. are anything that has one input (i.e. anon, view props)
			// exceptions: NOT, TRANSITION, CONSTANT, and non-view propositions.
			// add base, init to critical

			Log.println(print + " | remaining: " +
					Arrays.asList(p.getSize(),
							p.getNumLinks(),
							p.getBasePropositions().size()));

			boolean cont = false;
			for (int i = 0; i < print.size(); i++) {
				if (print.get(i) != 0) cont = true;
			}
			if (!cont) break;
		}
		Log.println("verifying propnet consistency");
		checkConsistency(p);
		Log.println("propnet optimization complete");
	}

	private static void checkConsistency(PropNet p) {
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
