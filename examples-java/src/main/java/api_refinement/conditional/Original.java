package api_refinement.conditional;

import static utils.Utils.*;

public class Original {
    public static int run() {
        int r = flipCoin();
        int ret;
        if (r == 0) {
            ret = 10;
        } else {
            ret = 20;
        }
        return ret;
    }
}
