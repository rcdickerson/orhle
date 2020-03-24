package param_usage.nondet_unused;

import static utils.Utils.*;

public class NondetUnused {
    public static int run(int param1, int param2) {
        int x = param1 + param2;
        int ret;
        if (flipCoin() == 0) {
            ret = x - param2;
        } else {
            ret = param1;
        }
        return ret;
    }
}
