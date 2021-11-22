#include <stdio.h>

// gvnpre cannot do LICM to a+b but sppregvn can
// gvnpre is not sure a+b is safe (may not go in to the loop)

int main(){
    int a = getchar();
    int b = getchar();

    for(int i=0; i<100; i++){
        if(i%10!=1){
            int c = a;
        }
        else{
            int  k = a+b;
        }

        int d = a+b;

    }



    return 0;
}