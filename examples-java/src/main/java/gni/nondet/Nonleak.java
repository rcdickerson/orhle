package gni.nondet;

import static utils.Utils.*;

public class Nonleak {
    public static int run(int high, int low) {
        int r = randInt(100);
        int ret;
        if (r == 5000) {
            ret = high + low;
        } else {
            ret = low;
        }
        return ret;
    }
}
