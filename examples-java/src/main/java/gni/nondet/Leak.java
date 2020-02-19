package gni.simple;

import static utils.Utils.*;

public class Leak {
    public static int run(int high, int low) {
        int r = randInt(100);
        int ret;
        if (r == 50) {
            ret = high + low;
        } else {
            ret = low;
        }
        return ret;
    }
}
