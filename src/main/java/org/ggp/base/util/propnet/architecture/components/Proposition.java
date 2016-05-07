package org.ggp.base.util.propnet.architecture.components;

import java.util.List;

import org.ggp.base.util.gdl.grammar.GdlSentence;
import org.ggp.base.util.propnet.architecture.Component;

/**
 * The Proposition class is designed to represent named latches.
 */
@SuppressWarnings("serial")
public final class Proposition extends Component {
	/** The name of the Proposition. */
	private GdlSentence name;
	public boolean base;

	/**
	 * Creates a new Proposition with name <tt>name</tt>.
	 *
	 * @param name
	 *            The name of the Proposition.
	 */
	public Proposition(GdlSentence name) {
		this.name = name;
		this.value = false;
	}

	/**
	 * Getter method.
	 *
	 * @return The name of the Proposition.
	 */
	public GdlSentence getName() {
		return name;
	}

	/**
	 * Setter method.
	 *
	 * This should only be rarely used; the name of a proposition is usually constant over its
	 * entire lifetime.
	 */
	public void setName(GdlSentence newName) {
		name = newName;
	}

	/**
	 * Returns the current value of the Proposition.
	 *
	 * @see org.ggp.base.util.propnet.architecture.Component#getValue()
	 */
	@Override
	public void propogate(boolean newValue) {
		if (base) return;
		value = newValue;
		if (value != lastPropogation) {
			lastPropogation = value;
			for (Component c : getOutputarr()){
				c.propogate(value);
			}
		}
	}
	
	public void makeMethod(StringBuilder file, List<Component> comps) {
		file.append("private void propagate" + comps.indexOf(this) + "(boolean newValue){\n");
		if (base) {
			file.append("return;}\n");
			return;
		}
		file.append("if (newValue != comps[" + comps.indexOf(this) + "]){\n");
		file.append("comps[" + comps.indexOf(this) + "] = newValue;\n");
		for (Component c : getOutputarr()) {
			file.append("propagate" + comps.indexOf(c) + "(newValue);\n");
		}
		file.append("}\n");
		file.append("}\n");
	}
	
	public void startPropogate() {
		lastPropogation = value;
		for (Component c : getOutputarr()){
			c.propogate(value);
		}
	}

	public void reset() {
		lastPropogation = false;
		value = false;
	}

	/**
	 * Setter method.
	 *
	 * @param value
	 *            The new value of the Proposition.
	 */
	public void setValue(boolean value) {
		this.value = value;
	}

	/**
	 * @see org.ggp.base.util.propnet.architecture.Component#toString()
	 */
	@Override
	public String toString() {
		return toDot("circle", value ? "red" : "white", name.toString());
	}
}