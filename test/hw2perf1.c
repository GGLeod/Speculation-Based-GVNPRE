#include <stdio.h>
#include <stdlib.h>

void hw2perf1(){
	long long A[1000];
	long long B[1000];
	long long C[1000];
	int i, j;
	for(i = 0; i < 1000; i++){
		A[i] = i * 2;
		B[i] = 0;
		C[i] = i * 1;
	}
	srand(2);

	j = 5;
	for(i = 0; i < 1000000000; i++) {
  		long long temp = (C[j] * 3 + 3948) / 27;
  		long long temp2 = temp * (temp / 93) * 2;
  		B[i % 1000] = (28 * A[j] / 3) * (temp2 / 45) * 4 + 279 + i;
  		if(i % 100000000 == 0) 
  			j = rand() % 1000;
	}

	for(i = 0; i < 1000; i++)
		printf("%f\n", B[i]);
}


int main() {

	hw2perf1();
	return 0;
}
