#include<stdio.h>
#include"ringbuffer.h"

int main()
{
	int i;
	for(i = 0;i < 10;i++)
		enq(i);
     	for(i = 0;i< 30;i++)
		printf("the data is %d:\n",deq());
	
	for(i = 0;i < 40;i++)
		enq(i);
	printf("the count head tail is %d %d %d\n",queue.count,queue.head,queue.tail);

}
