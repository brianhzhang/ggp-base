import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;

public class Log {
	private static PrintWriter file = null;

	public static void setFile(String fname) {
		if (!MyPlayer.USE_LOGGING) return;
		try {
			file = new PrintWriter(new FileWriter("logs/" + fname + ".txt", true), true);
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public static void printf(String fmt, Object... args) {
		if (file != null) file.printf(fmt, args);
		System.out.printf(fmt, args);
	}

	public static void println(Object s) {
		if (file != null) file.println(s);
		System.out.println(s);
	}

	public static void print(Object s) {
		if (file != null) file.print(s);
		System.out.print(s);
	}
}