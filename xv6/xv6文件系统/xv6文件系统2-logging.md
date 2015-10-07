####logging layer
code:log.c
文件系统中设计最有趣的地方就是崩溃恢复，设计这个log就是为了文件系统。如果一个崩溃发生在一系列写之间，可能发生数据不一致。

系统并不是直接写block，而是把命令先写在log上，然后操作，操作完成以后，标记上complte，这是原子操作。
如果崩溃发生了，恢复时，先检查log文件，有complete，则把这些操作执行。如果没有complete，则忽略log文件。

[1]
header block：记录log块号，和count
后面就是：data block
一次只能一个trans，xv6不允许并发的trans。
xv6允许并发的只读trans。
```
//Simple logging. Each system call that might write the file system
//should be surrounded with begin_trans() and commit_trans() calls.

//Read−only system calls don’t need to use transactions, though
//this means that they may observe uncommitted data. I−node and
//buffer locks prevent read−only calls from seeing inconsistent data.

struct logheader {
int n;
int sector[LOGSIZE];
};

struct log {
struct spinlock lock;
int start;
int size;
int busy; // a transaction is active
int dev;
struct logheader lh;
};

```
[2]
一般使用log的格式为：
```
begin_trans();
...
bp = bread();
bp->data[..] = ..;
log_write(bp);
...
commite_trans();
```

begin_trrans是这样写的：
```
void
begin_trans(void)
{
acquire(&log.lock);
while (log.busy) {
sleep(&log, &log.lock);
}
log.busy = 1;
release(&log.lock);
}

void
log_write(struct buf *b)
{
int i;
if (log.lh.n >= LOGSIZE || log.lh.n >= log.size − 1)
	panic("too big a transaction");
if (!log.busy)
	panic("write outside of trans");
for (i = 0; i < log.lh.n; i++) {
	if (log.lh.sector[i] == b−>sector) // log absorbtion?
		break;
}
log.lh.sector[i] = b−>sector;
struct buf *lbuf = bread(b−>dev, log.start+i+1);
memmove(lbuf−>data, b−>data, BSIZE);
bwrite(lbuf);
brelse(lbuf);
if (i == log.lh.n)
log.lh.n++;
b−>flags |= B_DIRTY; // XXX prevent eviction
}
```
commit_trans:首先，write_head,把count写到log的头部去。接着，执行install_trans把日志块儿里的数据读出来，写到正确的位置。接着，把log header写为0.
```
void
commit_trans(void)
{
if (log.lh.n > 0) {
	write_head();
	// Write header to disk −− the real commit
	install_trans(); 
	// Now install writes to home locations
	log.lh.n = 0;
	write_head();
	// Erase the transaction from the log
}
acquire(&log.lock);
log.busy = 0;
wakeup(&log);
release(&log.lock);
}

// Copy committed blocks from log to their home location
static void
install_trans(void)
{
int tail;
for (tail = 0; tail < log.lh.n; tail++) {
	struct buf *lbuf = bread(log.dev, log.start+tail+1); // read log block
	struct buf *dbuf = bread(log.dev, log.lh.sector[tail]); // read dst
	memmove(dbuf−>data, lbuf−>data, BSIZE); // copy block to dst
	bwrite(dbuf); // write dst to disk
	brelse(lbuf);
	brelse(dbuf);
}
}
```
至于错误恢复，过程是这样的。首先，在热和用户程序启动之前，启动过程之中，调用initlog，然后调用recove_from_log，如果commited,copy，然后clear头部。
PS：鸟哥的书，为什么日志有效
还有为什么挲是有效的
```
####logging layer
code:log.c
文件系统中设计最有趣的地方就是崩溃恢复，设计这个log就是为了文件系统。如果一个崩溃发生在一系列写之间，可能发生数据不一致。

系统并不是直接写block，而是把命令先写在log上，然后操作，操作完成以后，标记上complte，这是原子操作。
如果崩溃发生了，恢复时，先检查log文件，有complete，则把这些操作执行。如果没有complete，则忽略log文件。

[1]
header block：记录log块号，和count
后面就是：data block
一次只能一个trans，xv6不允许并发的trans。
xv6允许并发的只读trans。
```
//Simple logging. Each system call that might write the file system
//should be surrounded with begin_trans() and commit_trans() calls.

//Read−only system calls don’t need to use transactions, though
//this means that they may observe uncommitted data. I−node and
//buffer locks prevent read−only calls from seeing inconsistent data.

struct logheader {
int n;
int sector[LOGSIZE];
};

struct log {
struct spinlock lock;
int start;
int size;
int busy; // a transaction is active
int dev;
struct logheader lh;
};

```
[2]
一般使用log的格式为：
```
begin_trans();
...
bp = bread();
bp->data[..] = ..;
log_write(bp);
...
commite_trans();
```

begin_trrans是这样写的：
```
void
begin_trans(void)
{
acquire(&log.lock);
while (log.busy) {
sleep(&log, &log.lock);
}
log.busy = 1;
release(&log.lock);
}

void
log_write(struct buf *b)
{
int i;
if (log.lh.n >= LOGSIZE || log.lh.n >= log.size − 1)
	panic("too big a transaction");
if (!log.busy)
	panic("write outside of trans");
for (i = 0; i < log.lh.n; i++) {
	if (log.lh.sector[i] == b−>sector) // log absorbtion?
		break;
}
log.lh.sector[i] = b−>sector;
struct buf *lbuf = bread(b−>dev, log.start+i+1);
memmove(lbuf−>data, b−>data, BSIZE);
bwrite(lbuf);
brelse(lbuf);
if (i == log.lh.n)
log.lh.n++;
b−>flags |= B_DIRTY; // XXX prevent eviction
}
```
commit_trans:首先，write_head,把count写到log的头部去。接着，执行install_trans把日志块儿里的数据读出来，写到正确的位置。接着，把log header写为0.
```
void
commit_trans(void)
{
if (log.lh.n > 0) {
	write_head();
	// Write header to disk −− the real commit
	install_trans(); 
	// Now install writes to home locations
	log.lh.n = 0;
	write_head();
	// Erase the transaction from the log
}
acquire(&log.lock);
log.busy = 0;
wakeup(&log);
release(&log.lock);
}

// Copy committed blocks from log to their home location
static void
install_trans(void)
{
int tail;
for (tail = 0; tail < log.lh.n; tail++) {
	struct buf *lbuf = bread(log.dev, log.start+tail+1); // read log block
	struct buf *dbuf = bread(log.dev, log.lh.sector[tail]); // read dst
	memmove(dbuf−>data, lbuf−>data, BSIZE); // copy block to dst
	bwrite(dbuf); // write dst to disk
	brelse(lbuf);
	brelse(dbuf);
}
}
```
至于错误恢复，过程是这样的。首先，在热和用户程序启动之前，启动过程之中，调用initlog，然后调用recove_from_log，如果commited,copy，然后clear头部。
PS：鸟哥的书，为什么日志有效
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

// Loops (spins) until the lock is acquired.
// Holding a lock for a long time may cause
// other CPUs to waste time spinning to acquire it.
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

	// Record info about lock acquisition for debugging.
#ifdef DEBUG_SPINLOCK
	lk->cpu = thiscpu;
	get_caller_pcs(lk->pcs);
#endif
}


```
如果不把这些笔记作成电子版，以后怎么方便检索。
就像内敛会变，我呦忘记了。

