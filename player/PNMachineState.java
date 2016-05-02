import java.util.BitSet;
import java.util.HashSet;
import java.util.Set;

import org.ggp.base.util.gdl.grammar.GdlSentence;
import org.ggp.base.util.statemachine.MachineState;

public class PNMachineState extends MachineState {
	private BitSet bits;
	public PNMachineState(BitSet s) {
		this.bits = s;
	}

	public BitSet getBitContents() {
		return bits;
	}

	@Override
	public MachineState clone() {
		return new PNMachineState((BitSet) bits.clone());
	}

	/* Utility methods */
	@Override
	public int hashCode()
	{
		return bits.hashCode();
	}

	@Override
	public String toString()
	{
		if(bits == null)
			return "(PNMachineState with null contents)";
		else
			return bits.toString();
	}

	@Override
	public boolean equals(Object o)
	{
		if ((o != null) && (o instanceof PNMachineState))
		{
			PNMachineState state = (PNMachineState) o;
			return state.getBitContents().equals(getBitContents());
		}

		return false;
	}
}
