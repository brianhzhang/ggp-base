package org.ggp.base.util.propnet.architecture.components;

import java.util.List;

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

	public void makeMethod(StringBuilder file, List<Component> comps) {
		file.append("private void propagate" + comps.indexOf(this) + "(boolean newValue){\n");
		file.append("boolean next = ");
		file.append("!comps[" + comps.indexOf(getSingleInputarr()) + "];\n");

		file.append("if (next != comps[" + comps.indexOf(this) + "]){\n");
		file.append("comps[" + comps.indexOf(this) + "] = next;\n");
		for (Component c : getOutputarr()) {
			file.append("propagate" + comps.indexOf(c) + "(next);\n");
		}
		file.append("}\n");

		file.append("}\n");
	}

	@Override
	public void reset() {
		lastPropogation = false;
		value = false;
	}
}