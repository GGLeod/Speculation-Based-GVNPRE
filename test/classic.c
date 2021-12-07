#include <stdio.h>

// gvnpre cannot do LICM to a+b but sppregvn can
// gvnpre is not sure a+b is safe (may not go in to the loop)


void classic(){
    for(int i=0; i<100; i++){
        int a = i+1;
        int b = i/2;

        if(i%100==1){
            int c = a+1;
        }
        else{
            printf("%d", a+b);
        }

        if(i>90){
            int c = a+1;
        }
        else{
            printf("%d", a+b);
        }

    }

}


int main(){

    classic();


    return 0;
}