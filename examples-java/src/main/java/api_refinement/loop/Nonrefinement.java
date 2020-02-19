package api_refinement.loop;

import static utils.Utils.*;

public class Nonrefinement {
    public static int run() {
        int sum = 0;
        l: while (sum <= 100) {
            sum = sum + randInt(11);
        }
        return sum;
    }
}
