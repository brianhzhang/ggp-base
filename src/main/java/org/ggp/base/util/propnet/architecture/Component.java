package org.ggp.base.util.propnet.architecture;

import java.io.Serializable;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;

import org.ggp.base.util.propnet.architecture.components.Transition;

/**
 * The root class of the Component hierarchy, which is designed to represent
 * nodes in a PropNet. The general contract of derived classes is to override
 * all methods.
 */

public abstract class Component implements Serializable
{

	public boolean value = false;
	private static final long serialVersionUID = 352524175700224447L;
	/** The inputs to the component. */
	private Set<Component> inputs;
	/** The outputs of the component. */
	private Set<Component> outputs;

	private Component[] inputarr;
	private Component[] outputarr;
	
	protected boolean lastPropogation = false;

	/**
	 * Creates a new Component with no inputs or outputs.
	 */
	public Component()
	{
		this.inputs = new HashSet<Component>();
		this.outputs = new HashSet<Component>();
	}
	
	public double[] weights;
	public double[] inputval;
	public double outputval;
	public boolean visited = false;
	public double bias;
	
	public double calcValue() {
		if (this instanceof Transition) {
			return getSingleOutput().value ? 1. : 0.;
		}
		if (visited) {
			return outputval;
		}
		for (int i = 0; i < inputarr.length; i ++) {
			inputval[i] = inputarr[i].calcValue();
		}
		double sum = 0;
		for (int i = 0; i < inputarr.length; i ++) {
			sum += inputval[i] * weights[i];
		}
		visited = true;
		outputval = Math.max(0, sum + bias);
		return outputval;
	}
	
	public void passgradient(double dx, double lr) {
		if (this instanceof Transition) return;
		bias += dx * lr;
		for (int i = 0; i < inputarr.length; i ++) {
			if (inputval[i] > 0) inputarr[i].passgradient(weights[i] * dx, lr);
			weights[i] += inputval[i] * dx * lr;
		}
	}

	public void crystalize() {
		Random gen = new Random();
		inputarr = new Component[inputs.size()];
		inputs.toArray(inputarr);
		outputarr = new Component[outputs.size()];
		outputs.toArray(outputarr);
		inputval = new double[inputarr.length];
		weights = new double[inputarr.length];
		for (int i = 0; i < weights.length; i ++) {
			weights[i] = gen.nextDouble() * 0.1;
		}
		bias = gen.nextDouble() * 0.1;
	}

	/**
	 * Adds a new input.
	 *
	 * @param input
	 *            A new input.
	 */
	public void addInput(Component input)
	{
		inputs.add(input);
	}

	public void removeInput(Component input)
	{
		inputs.remove(input);
	}

	public void removeOutput(Component output)
	{
		outputs.remove(output);
	}

	public void removeAllInputs()
	{
		inputs.clear();
	}

	public void removeAllOutputs()
	{
		outputs.clear();
	}
	
	public abstract void makeMethod(StringBuilder file, List<Component> comps);

	/**
	 * Adds a new output.
	 *
	 * @param output
	 *            A new output.
	 */
	public void addOutput(Component output)
	{
		outputs.add(output);
	}

	/**
	 * Getter method.
	 *
	 * @return The inputs to the component.
	 */
	public Set<Component> getInputs()
	{
		return inputs;
	}
	
	public Component[] getInputarr() {
		return inputarr;
	}
	
	public Component getSingleInputarr() {
		assert inputarr.length == 1;
		return inputarr[0];
	}
	

	/**
	 * A convenience method, to get a single input.
	 * To be used only when the component is known to have
	 * exactly one input.
	 *
	 * @return The single input to the component.
	 */
	public Component getSingleInput() {
		assert inputs.size() == 1;
		return inputs.iterator().next();
	}

	/**
	 * Getter method.
	 *
	 * @return The outputs of the component.
	 */
	public Set<Component> getOutputs()
	{
		return outputs;
	}

	/**
	 * A convenience method, to get a single output.
	 * To be used only when the component is known to have
	 * exactly one output.
	 *
	 * @return The single output to the component.
	 */
	public Component getSingleOutput() {
		assert outputs.size() == 1;
		return outputs.iterator().next();
	}
	
	public Component[] getOutputarr() {
		return outputarr;
	}
	
	public Component getSingleOutputarr() {
		assert outputarr.length == 1;
		return outputarr[0];
	}

	/**
	 * Returns the value of the Component.
	 *
	 * @return The value of the Component.
	 */
	public boolean getValue() {
		return value;
	}

	public abstract void propogate(boolean newValue);

	/**
	 * Returns a representation of the Component in .dot format.
	 *
	 * @see java.lang.Object#toString()
	 */
	@Override
	public abstract String toString();

	public abstract void reset();

	/**
	 * Returns a configurable representation of the Component in .dot format.
	 *
	 * @param shape
	 *            The value to use as the <tt>shape</tt> attribute.
	 * @param fillcolor
	 *            The value to use as the <tt>fillcolor</tt> attribute.
	 * @param label
	 *            The value to use as the <tt>label</tt> attribute.
	 * @return A representation of the Component in .dot format.
	 */
	protected String toDot(String shape, String fillcolor, String label)
	{
		StringBuilder sb = new StringBuilder();

		sb.append("\"@" + Integer.toHexString(hashCode()) + "\"[shape=" + shape + ", value="+ value+", fillcolor=" + fillcolor + ", label=\"" + label + "\"]; ");
		for ( Component component : getOutputs() )
		{
			sb.append("\"@" + Integer.toHexString(hashCode()) + "\"->" + "\"@" + Integer.toHexString(component.hashCode()) + "\"; ");
		}

		return sb.toString();
	}

}