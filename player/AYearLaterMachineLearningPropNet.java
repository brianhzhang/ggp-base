import java.util.List;
import java.util.Map;
import java.util.Set;

import org.ggp.base.util.gdl.grammar.GdlConstant;
import org.ggp.base.util.gdl.grammar.GdlRelation;
import org.ggp.base.util.gdl.grammar.GdlSentence;
import org.ggp.base.util.propnet.architecture.Component;
import org.ggp.base.util.propnet.architecture.PropNet;
import org.ggp.base.util.propnet.architecture.components.Proposition;
import org.ggp.base.util.statemachine.Role;

public class AYearLaterMachineLearningPropNet {
	
	PropNet p;
	public static final double LEARNING_RATE = 0.001;
	public static final double INIT_SCALE = 0.5;
	
	public void initialize(PropNet p) {
		this.p = p;
		for (Component c : p.getComponents()) {
			c.crystalize();
		}
		for (GdlSentence s : p.getBasePropositions().keySet()) {
			p.getBasePropositions().get(s).isbase = true;
		}
	}
	
	//returns the loss
	public double trainOnce(PropNetMachineState s, JustKiddingPropNetStateMachine m, double[] goalValues) {
		double[] utilities = forwardPass(s, m);
		for (Component c : p.getComponents()) {
			c.trainvisited = false;
		}
		double loss = 0;
		List<Role> roles = p.getRoles();
		System.out.println("----------");
		System.out.println(utilities[0] + " " + utilities[1]);
		System.out.println(goalValues[0] + " " + goalValues[1]);
		Map<Role, Set<Proposition>> goals = p.getGoalPropositions();
		for (int i = 0; i < p.getRoles().size(); i ++) {
			Set<Proposition> goalprops = goals.get(roles.get(i));
			double denom = 0.0001;
			double[] scores = new double[goalprops.size()];
			int j = 0;
			double mseloss = utilities[i] > goalValues[i] ? -1 : 1;
			loss += Math.abs(utilities[i] - goalValues[i]);
			for (Proposition prop : goalprops) {
				double result = Math.exp(prop.calcValue());
				denom += result;
				scores[j] = result;
				j ++;
			}
			double ddenom = 0;
			j = 0;
			for (Proposition prop : goalprops) {
				ddenom += scores[j] * getGoalValue(prop) * mseloss * -1/(denom * denom);
				j ++;
			}
			j = 0;
			for (Proposition prop : goalprops) {
				int goalval = getGoalValue(prop);
				double dx = scores[j] * goalval * 1/denom * mseloss + 
						scores[j] * ddenom;
				System.out.println(prop.getName() + " " + dx);
				prop.passgradient(dx, LEARNING_RATE);
				j ++;
			}
		}
		return loss;
	}
	
	//returns a vector of scores
	public double[] forwardPass(PropNetMachineState s, JustKiddingPropNetStateMachine m) {
		List<Component> comps = m.components;
		int[] bases = m.basearr;
		for (int i = 0; i < s.props.length; i ++) {
			comps.get(bases[i] / 2).value = s.props[i];
		}
		for (Component c : p.getComponents()) {
			c.visited = false;
		}
		Map<Role, Set<Proposition>> goals = p.getGoalPropositions();
		List<Role> roles = p.getRoles();
		double[] average = new double[roles.size()];
		for (int i = 0; i < average.length; i ++) {
			Set<Proposition> goalprops = goals.get(roles.get(i));
			double denom = 0;
			double sum = 0;
			for (Proposition prop : goalprops) {
//				System.out.println(prop.bias + " " + prop.weights[0]);
				int goalval = getGoalValue(prop);
				double result = Math.exp(prop.calcValue());
				denom += result;
				sum += goalval * result;
			}
			average[i] = sum/denom;
		}
		return average;
	}
	
	private int getGoalValue(Proposition goalProposition) {
		GdlRelation relation = (GdlRelation) goalProposition.getName();
		GdlConstant constant = (GdlConstant) relation.get(1);
		return Integer.parseInt(constant.toString());
	}
}
