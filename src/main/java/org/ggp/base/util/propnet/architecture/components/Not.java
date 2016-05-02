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
	public void propogate(boolean newValue) {
		value = !getSingleInputarr().getValue();
		if (value != lastPropogation) {
			lastPropogation = value;
			for (Component c : getOutputarr()){
				c.propogate(value);
			}
		}
	}

	@Override
	public void reset() {
		lastPropogation = false;
		value = false;
	}
}