package api_refinement.loop;

import static utils.Utils.*;

public class Original {
    public static int run() {
        int sum = 0;
        l: while (sum <= 100) {
            sum = sum + randInt(10);
        }
        return sum;
    }
}
