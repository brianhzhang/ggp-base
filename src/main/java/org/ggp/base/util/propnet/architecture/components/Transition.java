package org.ggp.base.util.propnet.architecture.components;

import java.util.List;

import org.ggp.base.util.propnet.architecture.Component;

/**
 * The Transition class is designed to represent pass-through gates.
 */
@SuppressWarnings("serial")
public final class Transition extends Component
{
    /**
     * Returns the value of the input to the transition.
     *
     * @see org.ggp.base.util.propnet.architecture.Component#getValue()
     */
    @Override
    public void propogate(boolean newValue)
    {
        value = newValue;
        if (value != lastPropogation) {
			lastPropogation = value;
			for (Component c : getOutputarr()){
				c.propogate(value);
			}
		}
    }
    
    @Override
	public void makeMethod(StringBuilder file, List<Component> comps) {
    	file.append("private void propagate" + comps.indexOf(this) + "(boolean newValue){\n");
		file.append("if (newValue != comps[" + comps.indexOf(this) + "]){\n");
		file.append("comps[" + comps.indexOf(this) + "] = newValue;\n");
		for (Component c : getOutputarr()) {
			file.append("propagate" + comps.indexOf(c) + "(newValue);\n");
		}
		file.append("}\n");
		file.append("}\n");
	}
    
    public void reset() {
    	lastPropogation = false;
		value = false;
	}

    /**
     * @see org.ggp.base.util.propnet.architecture.Component#toString()
     */
    @Override
    public String toString()
    {
        return toDot("box", "grey", "TRANSITION");
    }
}