
#define SIZE 100
struct rb {
	int a[SIZE];
	int head;
	int tail;
} queue;

void
init() {
	queue.head = queue.tail = 0;	
}

int enq(int x) {
	if(queue.count == SIZE)
		return -1;
	queue.a[queue.head] = x;	
	queue.head = (queue.head + 1)%SIZE;
	queue.count++;
	return 0;
}

int deq() {
	int x;
	if(queue.count == 0)
		return -1;
	x = queue.a[queue.tail];
	queue.tail = (queue.tail + 1)%SIZE;
	queue.count--;
	return x;
}

