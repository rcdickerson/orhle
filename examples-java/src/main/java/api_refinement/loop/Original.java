package api_refinement.loop;

import static utils.Utils.*;

public class Original {
    public static int run() {
        int sum = 0;
        while (sum <= 100) {
            loopInvariant("(and (=> (<= Original!sum 100) (and (< 100 Refinement!sum) (< Refinement!sum 110))) (=> (< 100 Original!sum) (= Original!sum Refinement!sum)))");
            sum = sum + randInt(10);
        }
        return sum;
    }
}
