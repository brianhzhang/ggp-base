package org.ggp.base.util.propnet.architecture.components;

import org.ggp.base.util.propnet.architecture.Component;

/**
 * The And class is designed to represent logical AND gates.
 */
@SuppressWarnings("serial")
public final class And extends Component
{
    /**
     * Returns true if and only if every input to the and is true.
     *
     * @see org.ggp.base.util.propnet.architecture.Component#getValue()
     */
    @Override
    public void propogate()
    {
    	value = true;
        for ( Component component : getInputs() )
        {
            if ( !component.getValue() )
            {
                value = false;
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
        return toDot("invhouse", "grey", "AND");
    }

}
