package org.ggp.base.util.propnet.architecture.components;

import org.ggp.base.util.propnet.architecture.Component;

/**
 * The Or class is designed to represent logical OR gates.
 */
@SuppressWarnings("serial")
public final class Or extends Component
{
    /**
     * Returns true if and only if at least one of the inputs to the or is true.
     *
     * @see org.ggp.base.util.propnet.architecture.Component#getValue()
     */
    @Override
    public void propogate()
    {
    	value = false;
        for ( Component component : getInputs() )
        {
            if ( component.getValue() )
            {
                value = true;
                break;
            }
        }
        if (value != lastPropogation) {
			lastPropogation = value;
			for (Component c : getOutputs()){
				c.propogate();
			}
		}
    }
    
    public void reset() {
		value = false;
		lastPropogation = false;
	}
    /**
     * @see org.ggp.base.util.propnet.architecture.Component#toString()
     */
    @Override
    public String toString()
    {
        return toDot("ellipse", "grey", "OR");
    }
}