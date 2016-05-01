package org.ggp.base.util.propnet.architecture.components;

import org.ggp.base.util.propnet.architecture.Component;

/**
 * The Not class is designed to represent logical NOT gates.
 */
@SuppressWarnings("serial")
public final class Not extends Component
{

	public Not() {
		value = false;
		set = false;
	}
	
    /**
     * @see org.ggp.base.util.propnet.architecture.Component#toString()
     */
    @Override
    public String toString()
    {
        return toDot("invtriangle", "grey", "NOT");
    }

	@Override
	public void propogate() {
		value = !getSingleInput().getValue();
		if (!set || value != lastPropogation) {
			set = true;
			lastPropogation = value;
			for (Component c : getOutputs()){
				c.propogate();
			}
		}
	}

	@Override
	public void reset() {
		set = false;
		value = false;
	}
}