package api_refinement.conditional;

import static utils.Utils.*;

public class Refinement {
    public static int run() {
        int r = flipCoin();
        int ret;
        if (r == 0) {
            ret = 20;
        } else {
            ret = 10;
        }
        return ret;
    }
}
