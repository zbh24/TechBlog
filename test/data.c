//线性表的顺序结构
struct {
	int *base;
	int length;
	int size;
} sqlist;

//线性表的链式结构
struct Lnode {
	int data;
	struct Lnode *next;
} Lnode,*Linklist;


//栈
struct {
	int *base;
	int *top;
	int size;
} sqstack;


//队列

struct qnode {
	int data;
	struct qnode *next;
} qnode,*nodeptr;

struct {
	qnodeptr front;
	qnodeptr rear;
} linkqueue;


struct bitnode {
	int data;
	struct bitnode *left,*right;
} bitnode,*bitree;
