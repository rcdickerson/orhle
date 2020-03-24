package gni.denning;

import static utils.Utils.*;

public class Denning2 {
    public static void run(int f1_L, int f2_L, int f3_H, int f4_H) {
        int n = 0;
        int sum = 0;
        l: for (int i = 1; i <= 100; ++i) {
            int flag = f1_L;
            f2_L = flag;
            int x = f3_H;
            if (flag != 0) {
                n = n + 1;
                sum = sum + x;
            }
        }
        f2_L = n + sum + (sum / n);
        f1_L = f2_L;
    }
}
