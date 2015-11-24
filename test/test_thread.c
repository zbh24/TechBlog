#include<stdio.h>
#include<pthread.h>
#include<unistd.h>


int lock = 0;

static inline int
xchg(volatile int *addr, int newval)
{
	int result;

	// The + in "+m" denotes a read-modify-write operand.
	asm volatile("lock; xchgl %0, %1" :
			"+m" (*addr), "=a" (result) :
			"1" (newval) :
			"cc");
	return result;
}

void spinlock() {
	while (xchg(&lock,1) !=0)
		;
}

void spinunlock() {
	xchg(&lock,0);
}


int count = 0;

void add() {
	//spinlock();
	int i;
	int tmp = 0;
	for(i = 0; i < 10000000; i++) {
		tmp = tmp + 2;
		count = count + 2 ;
	}
	printf("The count address is :%p\n", &count);
	printf("The count is :%d\n\n", count);
	printf("The tmp address is :%p\n", &tmp);
	printf("The tmp is :%d\n", tmp);
	//spinunlock();
}

void min() {
	int i;
	for(i = 0; i < 5; i++) {
		count = count - 2;
		printf("The second  count is :%d\n", count);
		sleep(1);
	}

}

int main()
{

	pthread_t fst ,snd;
	void *ret;

	pthread_create(&fst,NULL,(void *(*)(void *))(add),NULL);
	pthread_create(&snd,NULL,(void *(*)(void *))(add),NULL);

	pthread_join(fst,&ret);
	pthread_join(snd,&ret);
	//printf("The count is :%d\n", count);

}
