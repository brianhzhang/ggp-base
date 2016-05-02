package org.ggp.base.util.propnet.architecture.components;

import org.ggp.base.util.propnet.architecture.Component;

/**
 * The Or class is designed to represent logical OR gates.
 */
@SuppressWarnings("serial")
public final class Or extends Component
{
	
	int numTrue = 0;
    /**
     * Returns true if and only if at least one of the inputs to the or is true.
     *
     * @see org.ggp.base.util.propnet.architecture.Component#getValue()
     */
    @Override
    public void propogate(boolean newValue)
    {
    	numTrue += (newValue)? 1 : -1;
    	value = (numTrue != 0);
        for ( Component component : getInputarr() )
        {
            if ( component.getValue() )
            {
                value = true;
                break;
            }
        }
        if (value != lastPropogation) {
			lastPropogation = value;
			for (Component c : getOutputarr()){
				c.propogate(value);
			}
		}
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
        return toDot("ellipse", "grey", "OR");
    }
}