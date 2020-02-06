package api_refinement.loop;

import static utils.Utils.*;

public class Refinement {
    public static int run() {
        int sum = 0;
        while (sum <= 100) {
            loopInvariant("(and (<= 0 Refinement!sum) (< Refinement!sum 110))");
            sum = sum + randOddInt(10);
        }
        return sum;
    }
}
