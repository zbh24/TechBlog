#include<stdio.h>

int main()
{
	int i = 0;
	for(i = 0; i < 2; i++) {
		fork();
		printf(".\n");
	}

}

//It will putput 6 dot.
