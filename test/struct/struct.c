#include<stdio.h>

struct buf {
	int value;
	struct buf *next;
} buffer[10];


int main() {
	struct buf x;
	struct buf *y;
	x.value = 1;
	printf("The value is:%d\n",x.value);
	
	y = &x;
	(*y).value = 2;
	printf("The value is:%d\n",x.value);
	
	y->value = 3;
	printf("The value is:%d\n",x.value);

	buffer[0].next = &x;
	printf("The value is:%d\n",(buffer[0].next)->value);
	
	buffer->next = &x;
	printf("The value is:%d\n",(buffer->next)->value);
}



//1.x的地址是跟x.value的地址相同的。
//2.指针存的是地址
//3.变量是x.value,指针是x->value
