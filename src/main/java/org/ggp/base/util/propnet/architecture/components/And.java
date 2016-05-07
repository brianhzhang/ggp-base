package org.ggp.base.util.propnet.architecture.components;

import java.util.List;

import org.ggp.base.util.propnet.architecture.Component;

/**
 * The And class is designed to represent logical AND gates.
 */
@SuppressWarnings("serial")
public final class And extends Component
{
	
	int numTrue = 0;
    /**
     * Returns true if and only if every input to the and is true.
     *
     * @see org.ggp.base.util.propnet.architecture.Component#getValue()
     */
    @Override
    public void propogate(boolean newValue)
    {
    	numTrue += (newValue)? 1 : -1;
    	value = (numTrue == getInputarr().length);
        if (value != lastPropogation) {
			lastPropogation = value;
			for (Component c : getOutputarr()){
				c.propogate(value);
			}
		}
    }
    
    public void makeMethod(StringBuilder file, List<Component> comps) {
    	file.append("private void propagate" + comps.indexOf(this) + "(boolean newValue){\n");
    	file.append("boolean next = ");
    	file.append("comps[" + comps.indexOf(getInputarr()[0]) + "]");
    	for (int i = 1; i < getInputarr().length; i ++) {
    		file.append(" && comps[" + comps.indexOf(getInputarr()[i]) + "]");
    	}
    	file.append(";\n");
    	
    	file.append("if (next != comps[" + comps.indexOf(this) + "]){\n");
		file.append("comps[" + comps.indexOf(this) + "] = next;\n");
		for (Component c : getOutputarr()) {
			file.append("propagate" + comps.indexOf(c) + "(next);\n");
		}
		file.append("}\n");
    	
    	file.append("}\n");
    }
    
    public void reset() {
		value = false;
		lastPropogation = false;
		numTrue = 0;
	}

    /**
     * @see org.ggp.base.util.propnet.architecture.Component#toString()
     */
    @Override
    public String toString()
    {
        return toDot("invhouse", "grey", "AND");
    }

}
