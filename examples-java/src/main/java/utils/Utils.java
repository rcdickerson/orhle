package utils;
import java.util.Random;

public class Utils {
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

    /**
     * @return either 0 or 1
     */
    public static int flipCoin() {
        return randInt(1);
    }
}