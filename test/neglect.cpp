#include <stdio.h>

// This PRE cannot be discovered by GVN
// In lexical version of PRE described by the paper
// it will treat a=a+1 and a as the same variable

int main(){
    int a = getchar();
    int b = getchar();

    for(int i=0; i<100; i++){
        if(i%10!=1){
            a = a +1;
        }
        else{
            printf("%d", a+b);
        }

        printf("%d", a+b);

    }



    return 0;
}