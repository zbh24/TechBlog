#include<stdio.h>
#include<pthread.h>
#include<unistd.h>

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

void spinlock(int *lock) {
	while (xchg(lock,1) !=0)
		;
}

void spinunlock(int *lock) {
	xchg(lock,0);
}


void P(int *p,int *count) {
	while ( *count <= 0)
		;
	spinlock(p);
	*count = *count - 1;
	spinunlock(p);

}


void V(int *v,int *count) {
	spinlock(v);
	*count = *count + 1;
	spinunlock(v);
}

/********************************************************************************/
/*										*/
/*										*/
/*										*/
/********************************************************************************/


int spin_full,spin_empty,spin_mutex1,spin_mutex2;
int full,empty;
int in,out;

void producer() {
	while(1) {
		P(&spin_full,&full);
	
		spinlock(&spin_mutex1);
		printf("The producer is:%d\n",in);
		in = (in + 1) % 5;
		spinunlock(&spin_mutex1);

		V(&spin_empty,&empty);
	}
}


void consumer() {
	while(1) {
		P(&spin_empty,&empty);
	
		spinlock(&spin_mutex2);
		printf("The consumer is:%d\n",out);
		out = (out + 1) % 5;
		spinunlock(&spin_mutex2);

		V(&spin_full,&full);
	}
}




int main() {

	int i = 0;	
	void *ret;
	pthread_t producerid[100],consumerid[100];

	spin_full = spin_empty = spin_mutex1 =spin_mutex2 = 0;
	full = 5;
	empty = 0;
	in = out = 0;
	
	while (i < 50 ) {
		pthread_create(&producerid[i],NULL,producer,NULL);
		pthread_create(&consumerid[i],NULL,consumer,NULL);
		i++;
	}
	i = 0;
	while (i < 50) { 
		pthread_join(producerid[i],&ret);
		pthread_join(consumerid[i],&ret);
		i++;
	}
	printf("Done");

}





