package param_usage.nondet_used;

import static utils.Utils.*;

public class NondetUsed {
    public static int run(int param1, int param2) {
        int x = param1 + param2;
        int ret;
        if (randInt(1) == 0) {
            ret = x;
        } else {
            ret = param1;
        }
        return ret;
    }
}
