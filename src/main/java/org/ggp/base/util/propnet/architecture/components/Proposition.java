package org.ggp.base.util.propnet.architecture.components;

import java.util.Set;

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
	public boolean input;
	private PropCallback setBases;
	private PropCallback setInput;

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

	public void setCallbacks(PropCallback bases, PropCallback inputs) {
		this.setBases = bases;
		this.setInput = inputs;
	}

	/**
	 * Returns the current value of the Proposition.
	 *
	 * @see org.ggp.base.util.propnet.architecture.Component#getValue()
	 */
	@Override
	public void propogate(boolean newValue) {
		if (base) {
			if (newValue != value) setBases.callback(this, newValue);
			return;
		}
		if (input) {
			if (newValue != value) setInput.callback(this, newValue);
			return;
		}
		Set<Component> components = getInputs();
		if (components.size() == 0) {
		} else {
			Component c = getSingleInput();
			if (c instanceof Transition) {
			} else {
				value = c.getValue();
			}
		}
		if (value != lastPropogation) {
			lastPropogation = value;
			for (Component c : getOutputs()){
				c.propogate(value);
			}
		}
	}

	public void startPropogate() {
		lastPropogation = value;
		for (Component c : getOutputs()){
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