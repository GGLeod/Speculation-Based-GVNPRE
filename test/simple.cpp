#include <stdio.h>

int main(){
    int a = getchar();
    int b = getchar();
    // for(int i=0; i<1000; i++){
        int c = 0;
        if(a%100!=1){
            c = c+a;
        }
        else{
            int  k = a+b;
            c = c+k;
        }

        if(b%200==1){
            c = c - b + 1;
        }
        else{
            int  k = a+b;
            c = c+k;
        }

        // a = a+1;
    // }


    return 0;
}