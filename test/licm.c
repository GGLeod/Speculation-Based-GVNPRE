#include <stdio.h>

// gvnpre cannot do LICM to a+b but sppregvn can
// gvnpre is not sure a+b is safe (may not go in to the loop)

void licm(int a, int b){
    for(int i=0; i<100; i++){
        if(i%10!=1){
            int c = a;
        }
        else{
            int  k = a+b;
            printf("%d", k);
        }

        printf("%d", a+b);

    }

}


int main(){
    licm(1, 2);
    return 0;
}