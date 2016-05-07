package org.ggp.base.util.propnet.architecture.components;

import java.util.List;

import org.ggp.base.util.propnet.architecture.Component;

/**
 * The Constant class is designed to represent nodes with fixed logical values.
 */
@SuppressWarnings("serial")
public final class Constant extends Component
{
    /** The value of the constant. */
    private final boolean value;

    /**
     * Creates a new Constant with value <tt>value</tt>.
     *
     * @param value
     *            The value of the Constant.
     */
    public Constant(boolean value)
    {
        this.value = value;
    }

    /**
     * Returns the value that the constant was initialized to.
     *
     * @see org.ggp.base.util.propnet.architecture.Component#getValue()
     */
    @Override
    public boolean getValue()
    {
        return value;
    }

    /**
     * @see org.ggp.base.util.propnet.architecture.Component#toString()
     */
    @Override
    public String toString()
    {
        return toDot("doublecircle", "grey", Boolean.toString(value).toUpperCase());
    }

	@Override
	public void reset() {}

	@Override
	public void propogate(boolean newValue) {
		for (Component c : getOutputarr()) {
			c.propogate(value);
		}
	}
	
	public void makeMethod(StringBuilder file, List<Component> comps) {
		file.append("private void propagate" + comps.indexOf(this) + "(boolean newValue){\n");
		for (Component c : getOutputarr()) {
			file.append("propagate" + comps.indexOf(c) + "(comps[" + comps.indexOf(this) + "]);\n");
		}
		file.append("}\n");
	}
}