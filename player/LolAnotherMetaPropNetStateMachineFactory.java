import java.net.URL;
import java.net.URLClassLoader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

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

public class LolAnotherMetaPropNetStateMachineFactory {
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
	public LolAnotherMetaPropNetStateMachineFactory(List<Gdl> description) {
		thing ++;
		p = null;
		try {
			p = OptimizingPropNetFactory.create(description);
		} catch (InterruptedException e) {
			e.printStackTrace();
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
		for (Component c : p.getComponents()) {
			c.crystalize();
		}
//		optimizePropNet(comps);
		StringBuilder file = new StringBuilder("class LMetaPNSM"+thing+" extends MetaPropNetStateMachine {\n");

		file.append("private boolean init = false;\n");
		file.append("private int[] comps;\n");
		file.append("private int[] structure;\n");

		file.append("public LMetaPNSM" + thing + "(){\n");
		createConstructor(file);
		file.append("}\n");
		
		createPropagate(file);

//		file.append("private void clear() {\n");
//		file.append("}\n");
		
		file.append("private void markbases(boolean[] bases) {\n");
		createPropagateBases(file);
		file.append("}\n");
		
		file.append("private void markinputs(boolean[] inputs) {\n");
		createPropagateInputs(file);
		file.append("}\n");

//		for (Component c : comps) {
//			c.makeMethod(file, comps);
//		}

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
		System.out.println(file);
		
//		int constant = 0;
//		for (Component c : comps) {
//			if (c instanceof Constant) constant ++;
//		}
//		System.out.println("Number of Constants: " + constant);
//		System.out.println("Number of Ands: " + p.getNumAnds());
//		System.out.println("Number of Ors: " + p.getNumOrs());
//		System.out.println("Number of Nots: " + p.getNumNots());

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
			//TODO Add creation of a different thing if compilation fails
			List<Diagnostic> diagnostics = diagnosticsCollector.getDiagnostics();

			for (Diagnostic d : diagnostics) {
				System.out.println(d.toString());
			}
		}
		// Load and instantiate compiled class.
		URLClassLoader classLoader = new URLClassLoader(new URL[0]);
		try {
			cls = classLoader.loadClass("LMetaPNSM"+thing);
		} catch (ClassNotFoundException e) {
			e.printStackTrace();
		}
	}
	
//	private void optimizePropNet(List<Component> comps) {
//		List<Component> toremove = new ArrayList<Component>();
//		for (Component c : comps) {
//			if (c instanceof Proposition) {
//				if (!(p.getBasePropositions().values().contains(c) || p.getLegalPropositions().values().contains(c) ||
//						p.getInputPropositions().values().contains(c) || p.getGoalPropositions().values().contains(c))) {
//					for (Component before : c.getInputs()) {
//						before.getOutputs().addAll(c.getOutputs());
//						before.removeOutput(c);
//					}
//					toremove.add(c);
//				}
//			} else if (c instanceof Not) {
//				if (c.getInputs().size() == 1 && c.getSingleInput().getOutputs().size() == 1) {
//					if (c.getSingleInput() instanceof And) {
//						((And)c.getSingleInput()).nand = true;
//						toremove.add(c);
//					} else if (c.getSingleInput() instanceof Or) {
//						((Or)c.getSingleInput()).nor = true;
//						toremove.add(c);
//					}
//				}
//			}
//		}
//		comps.removeAll(toremove);
//	}

	static SimpleJavaFileObject getJavaFileContentsAsString(StringBuilder javaFileContents){
		JavaObjectFromString javaFileObject = null;
		try{
			javaFileObject = new JavaObjectFromString("LMetaPNSM"+thing, javaFileContents.toString());
		}catch(Exception exception){
			exception.printStackTrace();
		}
		return javaFileObject;
	}

	private void createConstructor(StringBuilder file) {
		int count = 0;
		String firstArray = "";
		String structureArray = "";
		for (int i = 0; i < comps.size(); i ++) {
			firstArray += createComponent(comps.get(i)) + "," + ((p.getBasePropositions().values().contains(comps.get(i)) ||
					p.getInputPropositions().values().contains(comps.get(i))) ? "1" : "0")
					+ "," + count + ",";
			structureArray += comps.get(i).getOutputs().size() + ",";
			count ++;
			for (Component c : comps.get(i).getOutputs()) {
				count ++;
				structureArray += (comps.indexOf(c) * 3) + ",";
			}
		}
		file.append("int[] temp = {" + firstArray.substring(0, firstArray.length() - 1) + "};\n");
		file.append("int[] temp2 = {" + structureArray.substring(0, structureArray.length() - 1) + "};\n");
		file.append("comps = temp;\n");
		file.append("structure = temp2;\n");
//		for (Component c : comps) {
//			if (c instanceof Constant) {
//				file.append("propagate(" +  (comps.indexOf(c) * 3) + "," + (c.getValue()? 1 : -1) + ");\n");
//			}
//			if (c instanceof Not) {
//				file.append("propagate(" +  (comps.indexOf(c) * 3) + ", 1);\n");
//			}
//		}
		
		//TODO propagate constants and nots?
	}

	private String createComponent(Component c) {
		if (c instanceof Or) {
			return ((((Or)c).nor)? "0xFFFFFFFF" : "0x7FFFFFFF");
		} else if (c instanceof And) {
			return "0x" + Integer.toString(((((And)c).nand)?0:0x80000000) - c.getInputs().size(), 16).toUpperCase();
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
		file.append("markbases(bases);\n");
		file.append("return " + createStructure(p.getTerminalProposition().getSingleInput()) + ";\n");
	}

	//boolean[] next(boolean[] bases, boolean[] inputs)
	private void createNext(StringBuilder file) {
		file.append("markbases(bases);\n");
		file.append("markinputs(inputs);\n");
		for (Proposition prop : bases) {
			String s = "next[" + bases.indexOf(prop) + "] = " + getValue(prop.getSingleInput()) + ";\n";
			file.append(s);
		}
		file.append("return next;\n");
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
//		file.append("clear();\n");
		file.append("boolean[] result = {");
		for (int i = 0; i < basearr.length - 1; i ++) {
			file.append(basearr[i] + ", ");
		}
		file.append(basearr[basearr.length - 1] + "};\n");
		file.append("return result;\n");
	}

	//boolean[] legal(boolean[] bases, int role)
	private void createInput(StringBuilder file) {
		file.append("markbases(bases);\n");
		for (int i = 0; i < legals.size(); i ++) {
			for (int j = 0; j < roles.size(); j ++) {
				if (roles.get(j).getName().equals(legals.get(i).getName().getBody().get(0))) {
					String s = ("next[" + i + "] = role == " + j + " && " +
							getValue(legals.get(i).getSingleInput()) + ";\n");
					file.append(s);
					movelist.add(new Move(legals.get(i).getName().get(1)));
					legalPropositions.get(new Role((GdlConstant) legals.get(i).getName().getBody().get(0))).
					add(new Move(legals.get(i).getName().get(1)));
				}
			}
		}
		file.append("return next;\n");
	}

	//int goal(boolean[] bases, int role)
	private void createGoal(StringBuilder file) {
		file.append("markbases(bases);\n");
		for (int i = 0; i < goals.size(); i ++) {
			for (int j = 0; j < roles.size(); j ++) {
				if (roles.get(j).getName().equals(goals.get(i).getName().getBody().get(0))) {
					file.append("if (role == " + j + " && " + getValue(goals.get(i).getSingleInput()) + ")\n");
					file.append("\treturn " + getGoalValue(goals.get(i)) + ";\n");
				}
			}
		}
		file.append("return -1;\n");
	}

	private String getValue(Component c) {
		return "((comps[" + comps.indexOf(c) * 3 + "] >> 31) == 1)";
	}

	private void createPropagateBases(StringBuilder file) {
		int count = 0;
		int size = 0;
		for (int i = 0; i < bases.size(); i ++) {
			String s = "";
			s += ("if (" + getValue(bases.get(i)) + " != bases[" + i + "]){\n");
			s += "comps[" + (comps.indexOf(bases.get(i)) * 3) + "] = (bases[" + i + "]) ? 0x80000000 : 0;\n";
			for (Component c : bases.get(i).getOutputs())
				s += ("propagate(" + (comps.indexOf(c) * 3) + ", (bases[" + i + "])?1:-1);\n");
			s += ("}\n");
			size += s.length();
			if (size < 40000) {
				file.append(s);
			} else {
				count ++;
				size = s.length();
				file.append("markbases" + count + "(bases);\n}\n");
				file.append("private void markbases" + count + "(boolean[] bases){\n");
				file.append(s);
			}
		}
	}

	private void createPropagateInputs(StringBuilder file) {
		int size = 0;
		int count = 0;
		for (int i = 0; i < inputs.size(); i ++) {
			String s = "";
			s += ("if (" + getValue(inputs.get(i)) + " != inputs[" + i + "]){\n");
			s += "comps[" + (comps.indexOf(inputs.get(i)) * 3) + "] = (inputs[" + i + "]) ? 0xF0000000 : 0x0F00000;\n";
			for (Component c : inputs.get(i).getOutputs())
				s += ("propagate(" + (comps.indexOf(c) * 3) + ", (inputs[" + i + "])?1:-1);\n");
			s += ("}\n");
			size += s.length();
			if (size < 40000) {
				file.append(s);
			} else {
				count ++;
				size = s.length();
				file.append("markinputs" + count + "(inputs);\n}\n");
				file.append("private void markinputs" + count + "(boolean[] inputs){\n");
				file.append(s);
			}
		}
	}
	
	private String createStructure(Component c) {
		if (bases.contains(c)) {
			return "bases[" + bases.indexOf(((Proposition) c)) + "]";
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
	
	private void createPropagate(StringBuilder file) {
		file.append("private void propagate(int index, int newValue){\n");
		file.append("if (comps[index + 1] == 1) return;\n");
		file.append("int old = comps[index] >> 31;\n");
		file.append("comps[index] += newValue;\n");
		file.append("if (old != comps[index] >> 31){\n");
		file.append("old = (comps[index] >> 31) - old;\n");
		file.append("for (int i = 0; i < structure[comps[index + 2]]; i ++){\n");
		file.append("propagate(structure[comps[index + 2] + i + 1], old);\n");
		file.append("}\n");
		file.append("}\n");
		file.append("}\n");
	}

	private int getGoalValue(Proposition goalProposition) {
		GdlRelation relation = (GdlRelation) goalProposition.getName();
		GdlConstant constant = (GdlConstant) relation.get(1);
		return Integer.parseInt(constant.toString());
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
