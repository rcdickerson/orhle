package api_refinement.loop;

import static utils.Utils.*;

public class Nonrefinement {
    public static int run() {
        int sum = 0;
        while (sum <= 100) {
            loopInvariant("(and (<= 0 Refinement!sum) (< Refinement!sum 111))");
            sum = sum + randInt(11);
        }
        return sum;
    }
}
