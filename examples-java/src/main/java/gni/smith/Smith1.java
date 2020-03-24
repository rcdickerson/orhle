package gni.smith;

import static utils.Utils.*;

public class Smith1 {
    public static int run(int secret) {
        int ret;
        if (secret % 2 == 0) {
            ret = 0;
        } else {
            ret = 1;
        }
        return ret;
    }
}
