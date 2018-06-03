import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;

public class Log {
	private static PrintWriter file;

	public static void setFile(String fname) {
		try {
			file = new PrintWriter(new FileWriter("logs/" + fname + ".txt", true), true);
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public static void printf(String fmt, Object... args) {
		file.printf(fmt, args);
		System.out.printf(fmt, args);
	}

	public static void println(Object s) {
		file.println(s);
		System.out.println(s);
	}

	public static void print(Object s) {
		file.print(s);
		System.out.print(s);
	}
	
	public static void printerr(Object s) {
		file.println(s);
		System.err.println(s);
	}
}