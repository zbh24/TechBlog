#ATT的内联汇编
> asm ( 汇编语句  
    : 输出操作数     // 非必需  
    : 输入操作数     // 非必需  
    : 其他被污染的寄存器 // 非必需  
    );  
   
```
#include <stdio.h>  
  
int main()  
{  
    int a=1, b=2, c=0;   
    // 实现的是 c = a + b
    asm(  
        "addl %2, %0"       // 1  
        : "=g"(c)           // 2  
        : "0"(a), "g"(b)    // 3  
        : "memory");        // 4  
  
    printf("现在c是:%d\n", c);  
    return 0;  
}  
```
volatile:表示是可变的，去掉优化，不然优化可能会放到寄存器里面去，因为这样速度会变快，不过加了这句后，就不会放到寄存器里面去了。

1.第一行是汇编，ATT是从左到右的。从第二行输出开始，从0编号，从小到大，1，2，3，4，5

2.
- a,b,c,d,S,D 分别代表 eax,ebx,ecx,edx,esi,edi 寄存器
- r 上面的寄存器的任意一个（谁闲着就用谁）
- m 内存
- i 立即数（常量，只用于输入操作数）
- g 寄存器、内存、立即数 都行（gcc你看着办）
对于寄存器会用%%eax来表示

3.
第4行标出那些在汇编代码中修改了的、又没有在输入/输出列表中列出的寄存器，这样 gcc 就不会擅自使用这些"危险的"寄存器。还可以用 "memory" 表示在内联汇编中修改了内存，之前缓存在寄存器中的内存变量需要重新读取。

###例子
读取ebp
```
static __inline uint32_t
read_ebp(void)
{
	uint32_t ebp;
	__asm __volatile("movl %%ebp,%0" : "=r" (ebp));
	return ebp;
}

```
这就是加锁的概念，锁总线，只要交换是原子的就可以了，之所以要用xchg，就是为了防止是多cpu来竞争。
自旋锁的意思就是多个线程竞争，原地等待。交换是原子的这个很重要。

如果是单核cpu的话，可能就不需要这么麻烦了，比如我通过cpu的系统调用进去，在申请时不允许调度就可以了。
比如，中断也可以，这样的话,看谁申请成功了。

多核cpu就需要spin_lock，因为每个cpu都只能关自己的中断。因此，关中断无法保持全局互斥。需要一个全局互斥点，我们依赖的是总线。 每个cpu通过竞争总线来锁。
自旋锁也有很多实现，这是最简单的自旋锁了。
mcs，k42，stack_lock这都是自旋锁的算法。
自旋锁是一种互斥原语，使用忙等。

```
static inline uint32_t
xchg(volatile uint32_t *addr, uint32_t newval)
{
	uint32_t result;

	// The + in "+m" denotes a read-modify-write operand.
	asm volatile("lock; xchgl %0, %1" :
			"+m" (*addr), "=a" (result) :
			"1" (newval) :
			"cc");
	return result;
}

```

申请锁，进入临界区：
```
void
spin_lock(struct spinlock *lk)
{
#ifdef DEBUG_SPINLOCK
	if (holding(lk))
		panic("CPU %d cannot acquire %s: already holding", cpunum(), lk->name);
#endif

	// The xchg is atomic.
	// It also serializes, so that reads after acquire are not
	// reordered before it. 
	while (xchg(&lk->locked, 1) != 0)
		asm volatile ("pause");
}

```
放弃锁，出临界区：
```
void
spin_unlock(struct spinlock *lk)
{
	// The xchg serializes, so that reads before release are 
	// not reordered after it.  The 1996 PentiumPro manual (Volume 3,
	// 7.2) says reads can be carried out speculatively and in
	// any order, which implies we need to serialize here.
	// But the 2007 Intel 64 Architecture Memory Ordering White
	// Paper says that Intel 64 and IA-32 will not move a load
	// after a store. So lock->locked = 0 would work here.
	// The xchg being asm volatile ensures gcc emits it after
	// the above assignments (and after the critical section).
	xchg(&lk->locked, 0);
}
```
PS：现在的cpu可以直接，lk->locked=0了，因为已经不存在顺序反了。
