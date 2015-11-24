#include<stdio.h>

int count = 0;

void add() {

	for(int i = 0; i < 5; i++) {
		count = count + 2;
		printf("The fist count is :%d\n", count);
 		sleep(1);
	}

}

void min() {
	for(int i = 0; i < 5; i++) {
		count = count - 2;
		printf("The second  count is :%d\n", count);
		sleep(1);
	}

}

int main()
{
	int i = 0;
	if (fork()) {
		add();
  	} else {
		min();
		//add();
	}

	
	printf("The count is :%d\n", count);

}
