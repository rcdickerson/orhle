package utils;
import java.util.Random;

public class Utils {
    /**
     * Specifies the loop invariant
     * @param s a SMTLib string
     */
    public static void loopInvariant(String s) {}

    /**
     * @param max
     * @return a random integer from 0 until `max`
     */
    public static int randInt(int max) {
        return new Random().nextInt(max);
    }

    /**
     * @param max
     * @return a random odd integer from 0 until `max`
     */
    public static int randOddInt(int max) {
        return new Random().nextInt(max / 2) * 2 + 1;
    }
}
