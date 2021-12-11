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

    /* Permutation program, heavily recursive, written by Denny Brown. */
void Swap ( int *a, int *b ) {
	int t;
	t = *a;  *a = *b;  *b = t;
}
void Initialize (int permarray[7]) {
	int i;
	for ( i = 1; i <= 7; i++ ) {
	    permarray[i]=i-1;
	}
}
int Permute (int n, int permarray[7], int pctr) {   /* permute */
	int k;
	pctr = pctr + 1;
	if ( n!=1 )  {
	    pctr = Permute(n-1, permarray, pctr);
	    for ( k = n-1; k >= 1; k-- ) {
			Swap(&permarray[n],&permarray[k]);
			pctr = Permute(n-1, permarray, pctr);
			Swap(&permarray[n],&permarray[k]);
		}
    }
    return pctr;

}     /* permute */
void Perm ()    {   /* Perm */
    int i;
    int pctr = 0;
    int permarray[7];
    for ( i = 1; i <= 5; i++ ) {
		Initialize(permarray);
		pctr = Permute(7, permarray, pctr);
	}
    if ( pctr != 43300 )
	printf(" Error in Perm.\n");
	printf("%d\n", pctr);
}     /* Perm */
int main()
{
	int i;
	for (i = 0; i < 10000; i++) Perm();
	return 0;
}
