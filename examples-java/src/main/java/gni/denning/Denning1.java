package gni.denning;

import static utils.Utils.*;

public class Denning1 {
    public static int run(int f1_L, int f2_L, int f3_H, int f4_H) {
        int i = 1;
        int n = 0;
        int sum = 0;
        l: while (i <= 100) {
            int flag = f1_L;
            f2_L = flag;
            int x = f3_H;
            if (flag != 0) {
                n = n + 1;
                sum = sum + x;
            } else {}
            i = i + 1;
        }
        f4_H = n + sum + (sum / n);
    }
}
