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
struct node {
	struct node *left,*right;
	int val;
};
    /* Towers */ /*
    discsizrange = 1..maxcells; */
#define    stackrange	3
/*    cellcursor = 0..maxcells; */
struct    element {
	int discsize;
	int next;
};

void Quicksort( int a[], int l, int r) {
	/* quicksort the array A from start to finish */
	int i,j,x,w;
	i=l; j=r;
	x=a[(l+r) / 2];
	do {
	    while ( a[i]<x ) i = i+1;
	    while ( x<a[j] ) j = j-1;
	    if ( i<=j ) {
			w = a[i];
			a[i] = a[j];
			a[j] = w;
			i = i+1;    j= j-1;
		}
	} while ( i<=j );
	if ( l <j ) Quicksort(a,l,j);
	if ( i<r ) Quicksort(a,i,r);
}
void Quick (int run) {
    unsigned int sortlist[50000];


	unsigned int littlest = RAND_MAX;
	unsigned int biggest = 0;

	for(int i=0; i<50000; i++){
		sortlist[i] = rand();

		littlest = littlest < sortlist[i] ? littlest : sortlist[i];
		biggest = biggest < sortlist[i] ? sortlist[i] : biggest;
	}
    Quicksort(sortlist,1,49999);
    if ( (sortlist[1] != littlest) || (sortlist[49999] != biggest) )	printf ( " Error in Quick.\n");

	for(int i=0; i<10; i++){
		printf("%d\n", sortlist[run + i]);
	}  
	printf("\n");
	  
}
int main()
{
	int i;
	for (i = 0; i < 1000; i++) Quick(i);
	return 0;
}
