#include <stdio.h>

int main(){
    int a = 1;
    int b = 2;
    for(int i=0; i<1000; i++){
        int c = 0;
        if(i%100==1){
            c = c+i;
        }
        else{
            int  k = a+b;
            c = c+k;
        }

        if(i%200==1){
            c = c - i + 1;
        }
        else{
            int  k = a+b;
            c = c+k;
        }

        a = a+1;
    }


    return 0;
}