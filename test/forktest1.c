#include<stdio.h>
#include<sys/types.h>
#include<sys/wait.h>

int main()
{
	int pid;
	int status;
	if((pid == fork())) {
		waitpid(pid,&status,0);
		printf("this is father\n");
	} else {
		printf("this is a children\n");
	}
	
}
