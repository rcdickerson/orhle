package param_usage.semantically_unused;

import static utils.Utils.*;

public class SemanticallyUnused {
    public static int run(int param1, int param2) {
        int x = param1 + param2;
        int y = x - param2;
        return y;
    }
}
