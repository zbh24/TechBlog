#include<stdio.h>
#include<setjmp.h>

jmp_buf env;

int main() {
	int i = 1;
	int rc;
	rc = setjmp(env);
	printf("rc is %d\n", rc);

	if(rc == 0) {
		printf("Myself is return:%d\n\n",rc);
		i++;
		longjmp(env,2);
		//longjmp(env,1);
		printf("this should not be printed\n");
	} else if(rc == 1) {
		printf("the i is %d\n",i);
		printf("longjmp is return:%d\n",rc);
	}
	else {
		printf("the i is %d\n",i);
		printf("nothing is happen\n");
	}
}
