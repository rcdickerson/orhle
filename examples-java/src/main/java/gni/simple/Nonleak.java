package gni.simple;

import static utils.Utils.*;

public class Nonleak {
    public static int run(int high, int low) {
        int x = high + low;
        return x - high;
    }
}
