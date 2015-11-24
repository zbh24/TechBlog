#include<stdio.h>

int add () {
	s:printf("this is add\n");
	goto s;
	return 0;
}

int main()
{
	printf("start\n");
	add();
	s:getchar();

}
