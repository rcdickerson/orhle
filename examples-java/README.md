# Java Examples
## File format
### Verification Task
`task.jklive`:
```
forall: ClassName[1], ClassName[2];
exists: ClassName[3];

pre:  (= ClassName!1!input ClassName!2!input);
post: (= ClassName!2!return ClassName!3!return);

loopInvariants {
  ClassName[1].label: (...);
  ClassName[2].label: (...);
  ClassName[3].label: (...);
}

loopVariants {
  ClassName[1].label: (...);
  ClassName[2].label: (...);
  ClassName[3].label: (...);
}
```
### Java Program
`ClassName.java`:
```
public class ClassName {
    public static int run(int input) {
        int ret = 0;
        label: for (int i = 1; i < input; ++i) {
            ret = ret + 1;
        }
        return ret;
    }
}
```
