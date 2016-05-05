import java.io.IOException;
import java.net.URI;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.LinkedBlockingDeque;

import javax.tools.DiagnosticCollector;
import javax.tools.JavaCompiler;
import javax.tools.JavaCompiler.CompilationTask;
import javax.tools.JavaFileObject;
import javax.tools.SimpleJavaFileObject;
import javax.tools.StandardJavaFileManager;
import javax.tools.ToolProvider;

import org.ggp.base.util.gdl.grammar.Gdl;
import org.ggp.base.util.gdl.grammar.GdlConstant;
import org.ggp.base.util.gdl.grammar.GdlRelation;
import org.ggp.base.util.gdl.grammar.GdlSentence;
import org.ggp.base.util.propnet.architecture.Component;
import org.ggp.base.util.propnet.architecture.PropNet;
import org.ggp.base.util.propnet.architecture.components.And;
import org.ggp.base.util.propnet.architecture.components.Constant;
import org.ggp.base.util.propnet.architecture.components.Not;
import org.ggp.base.util.propnet.architecture.components.Or;
import org.ggp.base.util.propnet.architecture.components.Proposition;
import org.ggp.base.util.propnet.architecture.components.Transition;
import org.ggp.base.util.propnet.factory.OptimizingPropNetFactory;
import org.ggp.base.util.statemachine.Move;
import org.ggp.base.util.statemachine.Role;
import org.ggp.base.util.statemachine.implementation.prover.query.ProverQueryBuilder;
import org.python.modules.synchronize;

public class BetterMetaPropNetStateMachineFactory {
	List<Proposition> bases;
	List<Proposition> inputs;
	List<Proposition> goals;
	List<Proposition> legals;
	Map<GdlSentence, Integer> inputmap;
	Map<Proposition, Integer> goalMap;
	List<Component> comps;
	Class<?> cls;
	PropNet p;
	
	Set<Integer> found;

	Map<Role, List<Move>> legalPropositions;
	List<Move> movelist;

	@SuppressWarnings({ "rawtypes", "unchecked", "resource" })
	public BetterMetaPropNetStateMachineFactory(List<Gdl> description) {
		p = null;
		try {
			p = OptimizingPropNetFactory.create(description);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		for (Component c : p.getComponents()) {
			c.crystalize();
		}
		legalPropositions = new HashMap<Role, List<Move>>();
		for (Role r : p.getRoles()) {
			legalPropositions.put(r, new ArrayList<Move>());
		}
		comps = new ArrayList<Component>(p.getComponents());
		comps.removeAll(p.getPropositions());
		found = new HashSet<Integer>();
		for (int i = 0; i < comps.size(); i ++) {
			found.add(i);
		}
		movelist = new ArrayList<Move>();
		goals = new ArrayList<Proposition>();
		legals = new ArrayList<Proposition>();
		for (Role r : p.getRoles()) {
			goals.addAll(p.getGoalPropositions().get(r));
			legals.addAll(p.getLegalPropositions().get(r));
		}
		bases = new ArrayList<Proposition>(p.getBasePropositions().values());
		inputs = new ArrayList<Proposition>(p.getInputPropositions().values());
		inputmap = new HashMap<GdlSentence, Integer>();
		for (int i = 0; i < inputs.size(); i ++) {
			inputmap.put(inputs.get(i).getName(), i);
		}
		StringBuilder file = new StringBuilder("import java.util.Arrays;class MetaPNSM extends MetaPropNetStateMachine {\n");

		//private variables.
		file.append("private boolean init = false;\n");
		file.append("private boolean[] prevbases;\n");
		file.append("private boolean[] previnputs;\n");
		file.append("private int[] components;\n");

		//TODO constructor
		file.append("public MetaPNSM(){\n");
		createConstructor(file);
		file.append("}\n");

		file.append("boolean terminal(boolean[] bases){\n");
		createTerminal(file, p);
		file.append("}\n");

		file.append("boolean[] next(boolean[] bases, boolean[] inputs){\n");
		file.append("boolean[] next = new boolean[" + bases.size() + "];\n");
		System.out.println("Total chain length: " + createNext(file));
		file.append("}\n");

		file.append("boolean[] initial(){\n");
		createInit(file);
		file.append("}\n");

		file.append("boolean[] legal(boolean[] bases, int role){\n");
		file.append("boolean[] next = new boolean[" + inputs.size() + "];\n");
		createInput(file);
		file.append("}\n");

		file.append("int goal(boolean[] bases, int role){\n");
		createGoal(file);
		file.append("}\n");

		file.append("}\n");
		System.out.println(file);
		System.out.println((found.size() - comps.size()) + "  " + found);
		System.out.println(p.getPropositions().size());

		JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
		DiagnosticCollector diagnosticsCollector =
				new DiagnosticCollector();
		StandardJavaFileManager fileManager  =
				compiler.getStandardFileManager(diagnosticsCollector, null, null);
		JavaFileObject javaObjectFromString = getJavaFileContentsAsString(file);
		Iterable<JavaFileObject> fileObjects = Arrays.asList(javaObjectFromString);
		final Iterable<String> options = Arrays.asList( new String[] { "-d", "./bin"} );
		CompilationTask task = compiler.getTask(null, fileManager, diagnosticsCollector, options, null, fileObjects);
		long start = System.currentTimeMillis();
		Boolean result = task.call();
		if(result == true){
			System.out.println("Compilation has succeeded in " + (System.currentTimeMillis() - start) + "ms");
		}else{
			System.out.println("Compilation fails.");
		}
		// Load and instantiate compiled class.
		URLClassLoader classLoader = new URLClassLoader(new URL[0]);
		try {
			cls = classLoader.loadClass("MetaPNSM");
		} catch (ClassNotFoundException e) {
			e.printStackTrace();
		}
	}


	private void createConstructor(StringBuilder file) {
		file.append("int[] components = {");
		file.append(makeInit(comps.get(0)));
		for (int i = 1; i < comps.size(); i ++) {
			file.append(", " + makeInit(comps.get(i)));
		}
		file.append("};\n");
		file.append("this.components = components;\n");
		file.append("prevbases = new boolean[" + bases.size() + "];\n");
		file.append("previnputs = new boolean[" + inputs.size() + "];\n");
	}

	private String makeInit(Component c) {
		if (c instanceof Or) {
			return "0x7FFFFFFF";
		} else if (c instanceof And) {
			return "0x" + Integer.toString(0x80000000 - c.getInputs().size(), 16).toUpperCase();
		} else if (c instanceof Not) {
			return "0xFFFFFFFF";
		} else if (c instanceof Transition) {
			return "0x7FFFFFFF";
		} else {
			if (c.getValue())
			return "0xF0000000";
			else
				return "0x0F000000";
		}
	}

	static SimpleJavaFileObject getJavaFileContentsAsString(StringBuilder javaFileContents){
		JavaObjectFromString javaFileObject = null;
		try{
			javaFileObject = new JavaObjectFromString("MetaPNSM", javaFileContents.toString());
		}catch(Exception exception){
			exception.printStackTrace();
		}
		return javaFileObject;
	}

	private void createTerminal(StringBuilder file, PropNet p) {
		file.append("return " + createStructure(p.getTerminalProposition()) + ";\n");
	}

	private int createNext(StringBuilder file) {
		int count = 0;
		int size = 0;
		xorbases(file);
		xorinput(file);
		for (Proposition prop : bases) {
			String s = "next[" + bases.indexOf(prop) + "] = (components["
					+ comps.indexOf(prop.getSingleInput())+ "] >> 31) == 1;\n";
			found.remove(comps.indexOf(prop.getSingleInput()));
			size += s.length();
			if (size < 64000) {
				file.append(s);
			} else {
				count ++;
				size = 0;
				file.append("return next" + count + "(bases, inputs, next);}\n");
				file.append("boolean[] next" + count + "(boolean[] bases, boolean[] inputs, boolean[] next){\n" + s);
			}
		}
		file.append("prevbases = bases;\n");
		file.append("previnputs = inputs;\n");
		file.append("return next;\n");
		return count;
	}

	private void createInit(StringBuilder file) {
		boolean[] basearr = new boolean[bases.size()];
		p.getInitProposition().setValue(true);
		p.getInitProposition().propogate(false);
		Map<GdlSentence, Proposition> bases = p.getBasePropositions();
		for (GdlSentence s : bases.keySet()) {
			if (bases.get(s).getSingleInputarr().getValue()) basearr[this.bases.indexOf(bases.get(s))] = true;
		}
		p.getInitProposition().setValue(false);
		p.getInitProposition().propogate(false);
		file.append("boolean[] result = {");
		for (int i = 0; i < basearr.length - 1; i ++) {
			file.append(basearr[i] + ", ");
		}
		file.append(basearr[basearr.length - 1] + "};\n");
		file.append("return result;\n");
	}

	private int createInput(StringBuilder file) {
		int count = 0;
		int size = 0;
		xorbases(file);
		for (int i = 0; i < legals.size(); i ++) {
			String s;
			if (bases.contains(legals.get(i).getSingleInput())) {
				s = "next[" + i + "] = bases["
						+ bases.indexOf(legals.get(i).getSingleInput())+ "];\n";
			}
			else {
				s = "next[" + i + "] = (components["
						+ comps.indexOf(legals.get(i).getSingleInput())+ "] >> 31) == 1;\n";
				found.remove(comps.indexOf(legals.get(i).getSingleInput()));
			}
			size += s.length();
			movelist.add(new Move(legals.get(i).getName().get(1)));
			legalPropositions.get(new Role((GdlConstant) legals.get(i).getName().getBody().get(0))).
			add(new Move(legals.get(i).getName().get(1)));
			if (size < 64000) {
				file.append(s);
			} else {
				count ++;
				size = 0;
				file.append("return next" + count + "(bases, inputs, next);}\n");
				file.append("boolean[] next" + count + "(boolean[] bases, boolean[] inputs, boolean[] next){\n" + s);
			}
		}
		file.append("prevbases = bases;\n");
		file.append("return next;\n");
		return count;
	}

	/*
	 * movelist.add(new Move(legals.get(i).getName().get(1)));
					legalPropositions.get(new Role((GdlConstant) legals.get(i).getName().getBody().get(0))).
					add(new Move(legals.get(i).getName().get(1)));
	 */

	private void createGoal(StringBuilder file) {
		xorbases(file);
		for (int i = 0; i < goals.size(); i ++) {
			for (int j = 0; j < p.getRoles().size(); j ++) {
				if (p.getRoles().get(j).getName().equals(goals.get(i).getName().getBody().get(0))) {
					file.append("if ((role == " + j + ") && (components["
							+ comps.indexOf(goals.get(i).getSingleInput()) + "] >> 31 == 1))\n");
					file.append("\treturn " + getGoalValue(goals.get(i)) + ";\n");
					found.remove(comps.indexOf(goals.get(i).getSingleInput()));
				}
			}
		}
		file.append("prevbases = bases;\n");
		file.append("return -1;\n");
	}

	private int getGoalValue(Proposition goalProposition) {
		GdlRelation relation = (GdlRelation) goalProposition.getName();
		GdlConstant constant = (GdlConstant) relation.get(1);
		return Integer.parseInt(constant.toString());
	}

	private void xorbases(StringBuilder file) {
		file.append("boolean[] xorbases = new boolean[" + bases.size() + "];\n");
		file.append("for (int i = 0; i < " + bases.size() + "; i ++) {\n");
		file.append("xorbases[i] = (bases[i] && !prevbases[i]) || (!bases[i] && prevbases[i]);\n");
		file.append("}\n");
		file.append("int nextb = 0;\n");
		file.append("int tempb = 0;\n");
		//TODO forward propogate
		for (int i = 0; i < bases.size(); i ++) {
			file.append("if (xorbases[" + i + "]){\n");
			LinkedBlockingDeque<Component> queue = new LinkedBlockingDeque<Component>();
			Component input = bases.get(i).getSingleOutput();
			queue.add(input);
			file.append("nextb = (bases[" + i + "])?1:-1;\n");
			while (!queue.isEmpty()) {
				input = queue.poll();
				if (comps.contains(input)){
					file.append(generateOutput(input, "b"));
					for (Component c : input.getOutputs()) {
						queue.add(c);
					}
				} else {
					if (!bases.contains(input)) {
						for (Component c : input.getOutputs()) {
							queue.add(c);
						}
					}
				}
			}
			file.append("}\n");
		}
	}

	private void xorinput(StringBuilder file) {
		file.append("boolean[] xorinput = new boolean[" + inputs.size() + "];\n");
		file.append("for (int i = 0; i < " + inputs.size() + "; i ++) {\n");
		file.append("xorinput[i] = (!inputs[i] && previnputs[i]) || (inputs[i] && !previnputs[i]);\n");
		file.append("}\n");
		file.append("int nexti = 0;\n");
		file.append("int tempi = 0;\n");
		//TODO forward propogate
		for (int i = 0; i < legals.size(); i ++) {
			file.append("if (xorinput[" + i + "]){\n");
			if (p.getLegalInputMap().get(legals.get(i)).getOutputs().size() == 0) {
				file.append("}\n");
				continue;
			}
			Component input = p.getLegalInputMap().get(legals.get(i)).getSingleOutput();
			LinkedBlockingDeque<Component> queue = new LinkedBlockingDeque<Component>();
			queue.add(input);
			file.append("nexti = (inputs[" + i + "])?1:-1;\n");
			while (!queue.isEmpty()) {
				input = queue.poll();
				if (comps.contains(input)){
					file.append(generateOutput(input, "i"));
					for (Component c : input.getOutputs()) {
						queue.add(c);
					}
				} else {
					if (!bases.contains(input)) {
						for (Component c : input.getOutputs()) {
							queue.add(c);
						}
					}
				}
			}
			file.append("}\n");
		}
	}

	private String generateOutput(Component c, String thing) {
		String s = "";
		s += "temp" + thing + " = (components[" + comps.indexOf(c) + "] >> 31);\n";
		found.remove(comps.indexOf(c));
		s += "components[" + comps.indexOf(c) + "] += next" + thing + ";\n";
		s += "next" + thing + " = (components[" + comps.indexOf(c) + "] >> 31) - temp" + thing + ";\n";
		return s;
	}

	private String createStructure(Component c) {
		if (bases.contains(c)) {
			return "bases[" + bases.indexOf(c) + "]";
		} else if (inputs.contains(c)) {
			return "inputs[" + inputs.indexOf(c) + "]";
		} else if (c instanceof Proposition) {
			if (((Proposition) c).getName().toString().equals("init")) return "init";
			return createStructure(c.getSingleInput());
		} else if (c instanceof Transition) {
			return createStructure(c.getSingleInput());
		} else if (c instanceof Not) {
			return "(!" + createStructure(c.getSingleInput()) + ")";
		} else if (c instanceof Constant) {
			return "" + c.getValue();
		} else if (c instanceof And) {
			String s = "(";
			Iterator<Component> it = c.getInputs().iterator();
			Component next;
			for (next = it.next(); it.hasNext(); next = it.next()) {
				s += createStructure(next) + " && ";
			}
			return s + createStructure(next) + ")";
		} else if (c instanceof Or) {
			String s = "(";
			Iterator<Component> it = c.getInputs().iterator();
			Component next;
			for (next = it.next(); it.hasNext(); next = it.next()) {
				s += createStructure(next) + " || ";
			}
			return s + createStructure(next) + ")";
		}
		else return ""; //shouldn't get here ever.
	}

	public MetaPropNetStateMachine getNewMachine() {
		MetaPropNetStateMachine instance = null;
		try {
			instance = (MetaPropNetStateMachine) cls.newInstance();
		} catch (InstantiationException | IllegalAccessException e) {
			e.printStackTrace();
		}
		instance.init(p.getRoles(), inputmap, legalPropositions, movelist);
		return instance;
	}
}
