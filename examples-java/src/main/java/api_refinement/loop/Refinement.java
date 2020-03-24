package api_refinement.loop;

import static utils.Utils.*;

public class Refinement {
    public static int run() {
        int sum = 0;
        l: while (sum <= 100) {
            sum = sum + randOddInt(10);
        }
        return sum;
    }
}
