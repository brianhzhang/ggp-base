import java.util.Set;

import org.ggp.base.util.gdl.grammar.GdlSentence;
import org.ggp.base.util.propnet.architecture.components.Proposition;
import org.ggp.base.util.statemachine.MachineState;

public class PropNetMachineState extends MachineState {
	
	private Set<Proposition> propContents;
	
	public PropNetMachineState() {
		contents = null;
	}
	
	public PropNetMachineState(Set<GdlSentence> contents, Set<Proposition> propContents) {
		this.contents = contents;
		this.propContents = propContents;
	}
	
	public Set<Proposition> getPropContents() {
		return propContents;
	}
}
