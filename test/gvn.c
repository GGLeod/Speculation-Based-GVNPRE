#include <stdio.h>

// gvnpre cannot do LICM to a+b but sppregvn can
// gvnpre is not sure a+b is safe (may not go in to the loop)

void gvn(int a, int b){
    for(int i=0; i<100; i++){
        int c = a + 1;
        if(i%10!=1){
            c = i;
            printf("%d\n", c);
        }
        else{
            printf("%d\n", c + b);
        }
        int d = a + 1;
        printf("%d\n", d + b);

    }
}


int main(){

    gvn(1, 2);



    return 0;
}