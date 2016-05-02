package org.ggp.base.util.propnet.architecture.components;

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
        value = getSingleInput().getValue();
        if (value != lastPropogation) {
			lastPropogation = value;
			for (Component c : getOutputs()){
				c.propogate(value);
			}
		}
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