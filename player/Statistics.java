
public class Statistics {

	public static double mean(double[] x) {
		double sum = 0;
		for (int i = 0; i < x.length; i++) {
			sum += x[i];
		}
		return sum / x.length;
	}

	public static double stdev(double[] x) {
		double sum = 0;
		double mean = mean(x);
		for (int i = 0; i < x.length; i++) {
			double diff = x[i] - mean;
			sum += diff * diff;
		}
		return Math.sqrt(sum / x.length);
	}

	public static double pearsonr(double[] x, double[] y) {
		double sum = 0;
		double meanx = mean(x);
		double meany = mean(y);
		for (int i = 0; i < x.length; i++) {
			sum += (x[i] - meanx) * (y[i] - meany);
		}
		return sum / (x.length * stdev(x) * stdev(y));
	}

	public static Correlation linreg(double[] x, double[] y) {
		Correlation out = new Correlation();
		double r = pearsonr(x, y);
		out.rsq = r * r;
		out.m = r * stdev(y) / stdev(x);
		out.b = mean(y) - out.m * mean(x);
		out.t = r / Math.sqrt((1 - out.rsq) / (x.length - 2));
		if (!Double.isFinite(out.b) || !Double.isFinite(out.t)) out.rsq = out.m = out.b = out.t = 0;
		out.residues = new double[y.length];
		for (int i = 0; i < y.length; i++) {
			out.residues[i] = y[i] - (out.m * x[i] + out.b);
		}
		return out;
	}
}

class Correlation {
	public double m;
	public double b;
	public double rsq;
	public double t;
	public double[] residues;
}
