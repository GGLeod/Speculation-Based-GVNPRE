#include <stdio.h>

// gvnpre cannot do LICM to a+b but sppregvn can
// gvnpre is not sure a+b is safe (may not go in to the loop)

int main(){
    int a = getchar();
    int b = getchar();

    for(int i=0; i<100; i++){
        int c = a + 1;
        if(i%10!=1){
            c = getchar();
            printf("%d", c);
        }
        else{
            printf("%d", c + b);
        }
        int d = a + 1;
        printf("%d", d+b);

    }



    return 0;
}