#include<stdio.h>
#include<setjmp.h>

jmp_buf env;

int main() {
	int i = 1;
	int rc;
	rc = sigsetjmp(env,i);
	printf("rc is %d\n", rc);

	if(rc == 0) {
		printf("Myself is return:%d\n\n",rc);
		i++;
		siglongjmp(env,2);
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

/*********************************************************************/
/*想起来了，有几种情况，变量是不能回滾的。第一，是栈上的。第二，是    */
/*两次函数调用之间，值改变了。第三，没有声明是易变的.                  */
/*********************************************************************/
