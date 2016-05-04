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

public class MetaPropNetStateMachineFactory {
	Collection<Proposition> bases;
	Collection<Proposition> inputs;
	List<Proposition> goals;
	List<Proposition> legals;
	Map<GdlSentence, Integer> basemap;
	Map<GdlSentence, Integer> inputmap;
	Map<Proposition, Integer> goalMap;
	Class<?> cls;
	PropNet p;

	Map<Role, List<Move>> legalPropositions;
	List<Move> movelist;

	@SuppressWarnings({ "rawtypes", "unchecked", "resource" })
	public MetaPropNetStateMachineFactory(List<Gdl> description) {
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
		movelist = new ArrayList<Move>();
		goals = new ArrayList<Proposition>();
		legals = new ArrayList<Proposition>();
		for (Role r : p.getRoles()) {
			goals.addAll(p.getGoalPropositions().get(r));
			legals.addAll(p.getLegalPropositions().get(r));
		}
		bases = p.getBasePropositions().values();
		basemap = new HashMap<GdlSentence, Integer>();
		int i = 0;
		for (Proposition prop : bases) {
			basemap.put(prop.getName(), i);
			i ++;
		}
		inputs = p.getInputPropositions().values();
		inputmap = new HashMap<GdlSentence, Integer>();
		i = 0;
		for (Proposition prop : inputs) {
			inputmap.put(prop.getName(), i);
			i ++;
		}
		StringBuilder file = new StringBuilder("class MetaPNSM extends MetaPropNetStateMachine {\n");

		file.append("private boolean init = false;\n");
		file.append("boolean terminal(boolean[] bases){\n");
		createTerminal(file, p);
		file.append("}\n");

		file.append("boolean[] next(boolean[] bases, boolean[] inputs){\n");
		file.append("boolean[] next = new boolean[bases.length];\n");
		createNext(file);
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

	private void createNext(StringBuilder file) {
		for (Proposition prop : bases) {
			file.append("next[" + basemap.get(prop.getName()) + "] = " + createStructure(prop.getSingleInput()) + ";\n");
		}
		file.append("return next;\n");
	}

	private void createInit(StringBuilder file) {
		boolean[] basearr = new boolean[bases.size()];
		p.getInitProposition().setValue(true);
		p.getInitProposition().propogate(false);
		Map<GdlSentence, Proposition> bases = p.getBasePropositions();
		for (GdlSentence s : bases.keySet()) {
			if (bases.get(s).getSingleInputarr().getValue()) basearr[basemap.get(s)] = true;
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

	private void createInput(StringBuilder file) {
		for (int i = 0; i < legals.size(); i ++) {
			for (int j = 0; j < p.getRoles().size(); j ++) {
				if (p.getRoles().get(j).getName().equals(legals.get(i).getName().getBody().get(0))) {
					file.append("next[" + i + "] = role == " + j + " && " +
							createStructure(legals.get(i).getSingleInput())+ ";\n");
					movelist.add(new Move(legals.get(i).getName().get(1)));
					legalPropositions.get(new Role((GdlConstant) legals.get(i).getName().getBody().get(0))).
					add(new Move(legals.get(i).getName().get(1)));
				}
			}
		}
		file.append("return next;\n");
	}

	private void createGoal(StringBuilder file) {
		for (int i = 0; i < goals.size(); i ++) {
			for (int j = 0; j < p.getRoles().size(); j ++) {
				if (p.getRoles().get(j).getName().equals(goals.get(i).getName().getBody().get(0))) {
					file.append("if (role == " + j + " && "
							+ createStructure(goals.get(i).getSingleInput()) + ")\n");
					file.append("\treturn " + getGoalValue(goals.get(i)) + ";\n");
				}
			}
		}
		file.append("return -1;\n");
	}

	private int getGoalValue(Proposition goalProposition) {
		GdlRelation relation = (GdlRelation) goalProposition.getName();
		GdlConstant constant = (GdlConstant) relation.get(1);
		return Integer.parseInt(constant.toString());
	}

	private String createStructure(Component c) {
		if (bases.contains(c)) {
			return "bases[" + basemap.get(((Proposition) c).getName()) + "]";
		} else if (inputs.contains(c)) {
			return "inputs[" + inputmap.get(((Proposition) c).getName()) + "]";
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

class JavaObjectFromString extends SimpleJavaFileObject{
	private String contents = null;
	public JavaObjectFromString(String className, String contents) throws Exception{
		super(new URI(className), Kind.SOURCE);
		this.contents = contents;
	}
	public CharSequence getCharContent(boolean ignoreEncodingErrors) throws IOException {
		return contents;
	}
}
