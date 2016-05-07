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

import javax.tools.Diagnostic;
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

public class BetterMetaPropNetStateMachineFactory {
	List<Proposition> bases;
	List<Proposition> inputs;
	List<Proposition> goals;
	List<Proposition> legals;
	List<Role> roles;
	Class<?> cls;
	PropNet p;
	static int thing;
	ArrayList<Component> comps;

	Map<GdlSentence, Integer> inputmap;

	Map<Role, List<Move>> legalPropositions;
	List<Move> movelist;

	@SuppressWarnings({ "rawtypes", "unchecked", "resource" })
	public BetterMetaPropNetStateMachineFactory(List<Gdl> description) {
		thing ++;
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
		roles = new ArrayList<Role>(p.getRoles());
		for (Role r : roles) {
			legalPropositions.put(r, new ArrayList<Move>());
		}
		comps = new ArrayList<Component>(p.getComponents());
		movelist = new ArrayList<Move>();
		goals = new ArrayList<Proposition>();
		legals = new ArrayList<Proposition>();
		goals = new ArrayList<Proposition>();
		for (Role r : roles) {
			goals.addAll(p.getGoalPropositions().get(r));
			legals.addAll(p.getLegalPropositions().get(r));
		}
		bases = new ArrayList<Proposition>(p.getBasePropositions().values());
		inputs = new ArrayList<Proposition>(p.getInputPropositions().values());
		inputmap = new HashMap<GdlSentence, Integer>();
		for (Proposition p : inputs) {
			inputmap.put(p.getName(), inputs.indexOf(p));
		}
		for (Proposition prop : p.getPropositions()) {
			if (bases.contains(prop) || inputs.contains(prop)) {
				prop.base = true;
			}
		}
		StringBuilder file = new StringBuilder("class BMetaPNSM"+thing+" extends MetaPropNetStateMachine {\n");

		file.append("private boolean init = false;\n");
		file.append("private boolean[] comps;\n");
		//		file.append("private boolean[] lastbases;\n");
		//		file.append("private boolean[] lastinputs;\n");

		file.append("public BMetaPNSM" + thing + "(){\n");
		file.append("clear();\n");
		file.append("}\n");

		file.append("private void clear() {\n");
		createConstructor(file);
		file.append("}\n");

		for (Component c : comps) {
			c.makeMethod(file, comps);
		}

		file.append("boolean terminal(boolean[] bases){\n");
		createTerminal(file, p);
		file.append("}\n");

		file.append("boolean[] next(boolean[] bases, boolean[] inputs){\n");
		file.append("boolean[] next = new boolean[bases.length];\n");
		System.out.println("Total next chain length: " + createNext(file));
		file.append("}\n");

		file.append("boolean[] initial(){\n");
		createInit(file);
		file.append("}\n");

		file.append("boolean[] legal(boolean[] bases, int role){\n");
		file.append("boolean[] next = new boolean[" + inputs.size() + "];\n");
		System.out.println("Total input chain length: " + createInput(file));
		file.append("}\n");

		file.append("int goal(boolean[] bases, int role){\n");
		createGoal(file);
		file.append("}\n");

		file.append("}\n");
		System.out.println(file);
		int constant = 0;
		for (Component c : comps) {
			if (c instanceof Constant) constant ++;
		}
		System.out.println("Number of Constants: " + constant);
		System.out.println("Number of Ands: " + p.getNumAnds());
		System.out.println("Number of Ors: " + p.getNumOrs());
		System.out.println("Number of Nots: " + p.getNumNots());

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
			List<Diagnostic> diagnostics = diagnosticsCollector.getDiagnostics();

			for (Diagnostic d : diagnostics) {
				System.out.println(d.toString());
			}
		}
		// Load and instantiate compiled class.
		URLClassLoader classLoader = new URLClassLoader(new URL[0]);
		try {
			cls = classLoader.loadClass("BMetaPNSM"+thing);
		} catch (ClassNotFoundException e) {
			e.printStackTrace();
		}
	}

	static SimpleJavaFileObject getJavaFileContentsAsString(StringBuilder javaFileContents){
		JavaObjectFromString javaFileObject = null;
		try{
			javaFileObject = new JavaObjectFromString("BMetaPNSM"+thing, javaFileContents.toString());
		}catch(Exception exception){
			exception.printStackTrace();
		}
		return javaFileObject;
	}

	private void createConstructor(StringBuilder file) {
		//		file.append("int[] components = {");
		//		file.append(createComponent(comps.get(0)));
		//		for (int i = 1; i < comps.size(); i ++) {
		//			file.append(", " + createComponent(comps.get(i)));
		//		}
		//		file.append("};\n");
		//		file.append("comps = components;\n");

		//		file.append("lastbases = new boolean[" + bases.size() + "];\n");
		//		file.append("lastinputs = new boolean[" + inputs.size() + "];\n");
		file.append("comps = new boolean[" + comps.size() + "];\n");
		for (Component c : comps) {
			if (c instanceof Constant) {
				file.append("comps[" + comps.indexOf(c) + "] = " + c.getValue() + ";\n");
				file.append("propagate" + comps.indexOf(c) + "(" + c.getValue() + ");\n");
			}
			if (c instanceof Not) {
				file.append("propagate" + comps.indexOf(c) + "(true);\n");
			}
		}
	}

	private String createComponent(Component c) {
		if (c instanceof Or) {
			return "0x7FFFFFFF";
		} else if (c instanceof And) {
			return "0x" + Integer.toString(0x80000000 - c.getInputs().size(), 16).toUpperCase();
		} else if (c instanceof Not) {
			return "0xFFFFFFFF";
		} else if (c instanceof Transition) {
			return "0x7FFFFFFF";
		} else { //  instanceof Constant
			return (c.getValue()) ? "0xF0000000" : "0x0F000000";
		}
	}

	//boolean terminal(boolean[] bases)
	private void createTerminal(StringBuilder file, PropNet p) {
		file.append("return " + createStructure(p.getTerminalProposition()) + ";\n");
	}

	//boolean[] next(boolean[] bases, boolean[] inputs)
	private int createNext(StringBuilder file) {
		createPropogateBases(file);
		createPropogateInputs(file);
		int count = 0;
		int size = 0;
		for (Proposition prop : bases) {
			String s = "next[" + bases.indexOf(prop) + "] = " + getValue(prop.getSingleInput()) + ";\n";
			size += s.length();
			if (size < 32000) {
				file.append(s);
			} else {
				count ++;
				size = s.length();
				file.append("return next" + count + "(bases, inputs, next);}\n");
				file.append("boolean[] next" + count + "(boolean[] bases, boolean[] inputs, boolean[] next){\n" + s);
			}
		}
		file.append("return next;\n");
		return count;
	}

	private void createPropogation(StringBuilder file, Component c) {
		String s = "";
		for (Component next : c.getOutputs()) {
			s += recCreatePropogation("", next);
		}
		file.append("private void propogate" + comps.indexOf(c) + "(int pass){\n");
		if (s.length() != 0) {
			file.append("int newPass = comps[" + comps.indexOf(c) + "] >> 31;\n");
		}
		file.append("comps[" + comps.indexOf(c) + "] += pass;\n");
		if (s.length() != 0) {
			file.append("if ((comps[" + comps.indexOf(c) + "] >> 31) != newPass){\n");
			file.append("newPass = (comps[" + comps.indexOf(c) + "] >> 31) - newPass;\n");
			file.append(s);
			file.append("}\n");
		}
		file.append("}\n");
	}

	private String recCreatePropogation(String s, Component c) {
		if (comps.contains(c)) {
			s += ("propogate" + comps.indexOf(c) + "(newPass);\n");
		} else {
			if (!p.getInputPropositions().values().contains(c) && !p.getBasePropositions().values().contains(c)) {
				for (Component next : c.getOutputs()) {
					s += recCreatePropogation("", next);
				}
			}
		}
		return s;
	}

	//boolean[] initial()
	private void createInit(StringBuilder file) {
		boolean[] basearr = new boolean[bases.size()];
		p.getInitProposition().setValue(true);
		p.getInitProposition().startPropogate();
		for (Proposition p : bases) {
			if (p.getSingleInputarr().getValue()) basearr[bases.indexOf(p)] = true;
		}
		p.getInitProposition().setValue(false);
		p.getInitProposition().startPropogate();
		//		for (int i = 0; i < comps.size(); i ++) {
		//			if (comps.get(i) instanceof Not) {
		//				file.append("propogate" + i + "((" + getValue(comps.get(i).getSingleInput()) + ")? 1: -1);\n");
		//			}
		//		}
		file.append("clear();\n");
		file.append("boolean[] result = {");
		for (int i = 0; i < basearr.length - 1; i ++) {
			file.append(basearr[i] + ", ");
		}
		file.append(basearr[basearr.length - 1] + "};\n");
		file.append("return result;\n");
	}

	//boolean[] legal(boolean[] bases, int role)
	private int createInput(StringBuilder file) {
		createPropogateBases(file);
		int count = 0;
		int size = 0;
		for (int i = 0; i < legals.size(); i ++) {
			for (int j = 0; j < roles.size(); j ++) {
				if (roles.get(j).getName().equals(legals.get(i).getName().getBody().get(0))) {
					System.out.println("Legal: " + legals.get(i).getInputs().size());
					String s = ("next[" + i + "] = role == " + j + " && " +
							getValue(legals.get(i).getSingleInput()) + ";\n");
					size += s.length();
					if (size < 32000) {
						file.append(s);
					} else {
						count ++;
						size = s.length();
						file.append("return legal" + count + "(bases, role, next);}\n");
						file.append("boolean[] legal" + count + "(boolean[] bases, int role, boolean[] next){\n" + s);
					}
					movelist.add(new Move(legals.get(i).getName().get(1)));
					legalPropositions.get(new Role((GdlConstant) legals.get(i).getName().getBody().get(0))).
					add(new Move(legals.get(i).getName().get(1)));
				}
			}
		}
		file.append("return next;\n");
		return count;
	}

	//int goal(boolean[] bases, int role)
	private void createGoal(StringBuilder file) {
		createPropogateBases(file);
		for (int i = 0; i < goals.size(); i ++) {
			for (int j = 0; j < roles.size(); j ++) {
				if (roles.get(j).getName().equals(goals.get(i).getName().getBody().get(0))) {
					System.out.println("Goals: " + goals.get(i).getInputs().size());
					file.append("if (role == " + j + " && " + getValue(goals.get(i).getSingleInput()) + ")\n");
					file.append("\treturn " + getGoalValue(goals.get(i)) + ";\n");
				}
			}
		}
		file.append("return -1;\n");
	}

	private String getValue(Component c) {
		//		if (bases.contains(c)) {
		//			return "bases[" + bases.indexOf(c) + "]";
		//		} else if (inputs.contains(c)) {
		//			return "inputs[" + inputs.indexOf(c) + "]";
		//		} else if (comps.contains(c)) {
		//			return "(comps[" + comps.indexOf(c) + "] >> 31) == 1";
		//		} else {
		//			String s = "";
		//			for (Component next : c.getInputs()) {
		//				s += getValue(next) + "||";
		//			}
		//			return s.substring(0, s.length() - 2);
		//		}
		return "comps[" + comps.indexOf(c) + "]";
	}

	private void createPropogateBases(StringBuilder file) {
		//		for (int i = 0; i < bases.size(); i ++) {
		//			if (comps.contains(bases.get(i).getSingleOutput())) {
		//				file.append("if (bases[" + i + "] ^ lastbases[" + i + "]){\n");
		//				file.append("propogate" + comps.indexOf(bases.get(i).getSingleOutput()) + "((bases[" + i + "])? 1:-1);\n");
		//				file.append("}\n");
		//			}
		//		}
		//		file.append("lastbases = bases;\n");
		for (int i = 0; i < bases.size(); i ++) {
			file.append("if (comps[" + comps.indexOf(bases.get(i)) + "] != bases[" + i + "]){\n");
			file.append("comps[" + comps.indexOf(bases.get(i)) + "] = bases[" + i + "];\n");
			for (Component c : bases.get(i).getOutputs())
				file.append("propagate" + comps.indexOf(c) + "(bases[" + i + "]);\n");
			file.append("}\n");
		}
	}

	private void createPropogateInputs(StringBuilder file) {
		//		for (int i = 0; i < inputs.size(); i ++) {
		//			if (inputs.get(i).getOutputs().size() == 0) continue;
		//			if (comps.contains(inputs.get(i).getSingleOutput())) {
		//				file.append("if (inputs[" + i + "] ^ lastinputs[" + i + "]){\n");
		//				file.append("propogate" + comps.indexOf(inputs.get(i).getSingleOutput()) + "((inputs[" + i + "])? 1:-1);\n");
		//				file.append("}\n");
		//			}
		//		}
		//		file.append("lastinputs = inputs;\n");
		for (int i = 0; i < inputs.size(); i ++) {
			file.append("if (comps[" + comps.indexOf(inputs.get(i)) + "] != inputs[" + i + "]){\n");
			file.append("comps[" + comps.indexOf(inputs.get(i)) + "] = inputs[" + i + "];\n");
			for (Component c : inputs.get(i).getOutputs())
				file.append("propagate" + comps.indexOf(c) + "(inputs[" + i + "]);\n");
			file.append("}\n");
		}
	}

	private int getGoalValue(Proposition goalProposition) {
		GdlRelation relation = (GdlRelation) goalProposition.getName();
		GdlConstant constant = (GdlConstant) relation.get(1);
		return Integer.parseInt(constant.toString());
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
		instance.init(roles, inputmap, legalPropositions, movelist);
		return instance;
	}
}
