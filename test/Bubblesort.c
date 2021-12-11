
#include <stdio.h>
#include <stdlib.h>
#define  nil		0
#define	 false		0
#define  true		1
#define  bubblebase	1.61f
#define  dnfbase 	3.5f
#define  permbase 	1.75f
#define  queensbase 1.83f
#define  towersbase 2.39f
#define  quickbase 	1.92f
#define  intmmbase 	1.46f
#define  treebase 	2.5f
#define  mmbase 	0.0f
#define  fpmmbase 	2.92f
#define  puzzlebase	0.5f
#define  fftbase 	0.0f
#define  fpfftbase 	4.44f
    /* Towers */
#define maxcells 	 18
    /* Intmm, Mm */
#define rowsize 	 40
    /* Puzzle */
#define size	 	 511
#define classmax 	 3
#define typemax 	 12
#define d 		     8
    /* Bubble, Quick */
#define sortelements 5000
#define srtelements  500
    /* fft */
#define fftsize 	 256 
#define fftsize2 	 129  
/*
type */
    /* Perm */
#define permrange     10
   /* tree */


void Bubblesort(int run) {
	int i, j;
	unsigned int sortlist[5000];


	unsigned int littlest = RAND_MAX;
	unsigned int biggest = 0;

	for(int i=0; i<5000; i++){
		sortlist[i] = rand();

		littlest = littlest < sortlist[i] ? littlest : sortlist[i];
		biggest = biggest < sortlist[i] ? sortlist[i] : biggest;
	}

	int top = 4999;
	
	while ( top>0 ) {
		
		i=0;
		while ( i<top ) {
			
			if ( sortlist[i] > sortlist[i+1] ) {
				j = sortlist[i];
				sortlist[i] = sortlist[i+1];
				sortlist[i+1] = j;
			}
			i=i+1;
		}
		
		top=top-1;
	}
	if ( (sortlist[0] != littlest) || (sortlist[4999] != biggest) )
	printf ( "Error3 in Bubble.\n");
	printf("%d\n", sortlist[run + 1]);
}
int main()
{
	int i;
	for (i = 0; i < 100; i++) Bubblesort(i);
	return 0;
}
