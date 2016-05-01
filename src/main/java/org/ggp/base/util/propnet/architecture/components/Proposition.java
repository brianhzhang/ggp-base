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
	/** The value of the Proposition. */
	private boolean value;
	private boolean set = false;

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
	public boolean getValue() {
		if (set) return value;
		Set<Component> components = getInputs();
		if (components.size() == 0) {
			return value;
		}
		Component c = getSingleInput();
		if (c instanceof Transition) {
			return value;
		}
		boolean val = c.getValue();
		return val;
	}
	
	public void setSet(boolean set) {
		this.set = set;
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