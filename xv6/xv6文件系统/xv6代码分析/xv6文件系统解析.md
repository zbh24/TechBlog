#xv6文件系统解析

####C语言前提
1.static 加在函数和外部变量是前是隐藏，加在内部变量是只初始化一次，一直存在。

2.程序和运行时环境。

3.enum months {jan = 1, feb,mar} a b c;
a = jan;
b = mar;

months x;
x = feb;

3.
```
void
panic(char *s)
{
	printf(2, "%s\n", s);
	exit();
}

int
fork1(void)
{
	int pid;
	pid = fork();
	if(pid == -1)
	     panic("fork");
	 return pid;
}

```
###ide.c
[1]
```
//PAGEBREAK!
// Wake up all processes sleeping on chan.
// The ptable lock must be held.
static void
wakeup1(void *chan)
{
  struct proc *p;

  for(p = ptable.proc; p < &ptable.proc[NPROC]; p++)
    if(p->state == SLEEPING && p->chan == chan)
      p->state = RUNNABLE;
}

// Wake up all processes sleeping on chan.
void
wakeup(void *chan)
{
  acquire(&ptable.lock);
  wakeup1(chan);
  release(&ptable.lock);
}

// Per-process state
struct proc {
  uint sz;                 // Size of process memory 
  pde_t* pgdir;           // Page table
  char *kstack;    
  enum procstate state;        // Process state
  int pid;                     // Process ID
  struct proc *parent;         // Parent process
  struct trapframe *tf; // Trap frame for syscall
  struct context *context;     // swtch() here 
  void *chan;     // If non-zero, sleeping on chan
  int killed;     // If non-zero, have been killed
  struct file *ofile[NOFILE];  // Open files
  struct inode *cwd;           // Current directory
  char name[16];               // Process name 
};

// Atomically release lock and sleep on chan.
// Reacquires lock when awakened.
void
sleep(void *chan, struct spinlock *lk)
{
  if(proc == 0)
    panic("sleep");

  if(lk == 0)
    panic("sleep without lk");

  // Must acquire ptable.lock in order to
  // change p->state and then call sched.
  // Once we hold ptable.lock, we can be
  // guaranteed that we won't miss any wakeup
  // (wakeup runs with ptable.lock locked),
  // so it's okay to release lk.
  if(lk != &ptable.lock){  //DOC: sleeplock0
    acquire(&ptable.lock);  //DOC: sleeplock1
    release(lk);
  }

  // Go to sleep.
  proc->chan = chan;
  proc->state = SLEEPING;
  sched();

  // Tidy up.
  proc->chan = 0;

  // Reacquire original lock.
  if(lk != &ptable.lock){  //DOC: sleeplock2
    release(&ptable.lock);
    acquire(lk);
  }
}

```
PS：总结sleep和wakeup：
- wakeup(b)就是唤醒所有沉睡在这个资源上的线程。
- sleep(b,&lock),就是在这个资源上沉睡，然后睡觉，等待别人把它唤醒。它对锁没有任何影响，因为它虽然先释放了，后来又申请了。
PS：它在沉睡期间，把锁给释放了，所以，其他人可以操作，不过醒来以后，又申请了。

[2]

```
struct buf {
  int flags;
  uint dev;
  uint blockno;
  struct buf *prev; // LRU cache list
  struct buf *next;
  struct buf *qnext; // disk queue
  uchar data[BSIZE];
};
```

这个里面有个struct buf *idequeue,这是个idequeue就是要处理的buffer，
idequeue->qnext就是要处理的buffer。如果idequeue是空的话，现在，就需要写新的buffer。

主要是的iderw，通过调用idestart来进行读写，调用idestart之前，必须通过idelock来把idestart锁住。然后这个disk锁叫idelock。

关于读写硬盘的三个函数。iderw,idestart，ideintr。另外还有个队列idequeue。
- iderw:这个最重要。iderw(b)
1）首先必须是busy的，不能是valid的，如果是valid，则什么也不做。
2）然后，加到idequeque。
3）如果当前只有这b了的话，那么就启动这个b。
4）否则，一直等到这个b变成valid。
- iderstart:如果是dirty的话，则直接写进去。否则的话，则通过调用中断ideintr读到idequeue.。只要idequeue不为空，会一直调用idestart会进行读或者写。
- ideintr：中断，会写把数据读到idequeue里面，然后继续处理下一个。

###bio.c
```
struct {
  struct spinlock lock;
  struct buf buf[NBUF];

  // Linked list of all buffers, through prev/next.
  // head.next is most recently used.
  struct buf head;
} bcache;

struct buf {
  int flags;
  uint dev;
  uint sector;
  struct buf *prev; // LRU cache list
  struct buf *next;
  struct buf *qnext; // disk queue
  uchar data[512];
};
```
通过bachche.head来把所有的buf来串起来。

buf有三种状态：
- busy:被一些程序给locked了,只要通过bread，而且没有通过brelse，一定是busy的
- valid:已经被disk读出数据来了，意思是可以用
- dirty:需要被写回disk

[1]
bget(dev,sector)
如果找到扇区，不是busy的话，设置为busy。否则busy的话，等待sleep。
如果没找到扇区，回收一个valid的，然后清除其它flags，设为busy。

[2]
bread(dev,sector)
最后得到一个标志位为busy和valid且对应的扇区。

[3]
bwrite(b)
首先，它必须是busy的。
然后就设置为drity，调用iderw写回去。

[4]
brelse(b)
释放一个busy的b，然后把这buffer移到bache.head.next里面去。
然后设置为非busy。

**总结**：其实，我们大可不必关心ide层，我们只要知道bread和bwrite会得到什么就OK了。

####log.c
```
struct logheader {
  int n;   
  int sector[LOGSIZE];
};

struct log {
  struct spinlock lock;
  int start;
  int size;
  int outstanding; // how many FS sys calls are executing.
  int committing;  // in commit(), please wait.
  int dev;
  struct logheader lh;
};
struct log log;
```
[1]
initlog函数：
这个函数初始化了锁，然后记录了log的start块儿和size块儿，就是哪里开始，有多少块儿，还有dev。

[2]
install_trans函数：
这个函数就是根据当前内存中的log，把日志块儿，先是写到对应的数据块儿的buffer里面，再写到数据块的disk里面。

[3]
read_head函数：
把那些disk里面的logheader读到当前内存中的logheader。

[4]
write_head函数：
把当前内存的logheader写到disk中的log的start块儿里面去

[5]
recover_from_log函数：
先是读取disk里面的logheader
然后把log块儿从log块儿写到数据块儿
然后把内存的logheader设置为0
写回到disk块儿里面

[6]
begin_trans函数：
把log设置为busy，这样其它就不能访问了。
PS:这个设计为什么不用锁
还有，有的地方不用自旋锁，而是用wakeup和sleep，有什么好处吗。

[7]
commit_trans函数：
根据内存中的log'，先写头部，然后安装日志块儿，内存头部设置为0，写到硬盘头部。
然后设置为非busy

[8]
log_write函数：
先把数据写到log层里面的disk里面。
然后标记这个buffer已经dirty了。

总结：
一个系统调用应该这么做：
```
begin_trans:
...
bp = bread();
bp->data[] = ...
logwrite(bp);
...

commit_trans();
```

只有revovery和commit的时候，才会install_trans，其它时候都不关心。
他们区别是一个不需要读disk的head。
这个buf队列里面，既有data block，也有log block。

logwrite：它是这样的，你修改好的buf数据，我写到日志块儿里面去。
所以，你读脏数据的时候，我也不担心，因为你永远都是直接先修改data 的buf的，这样就不存在这个问题了。

**总结**：
两个问题
1)不用担心数据不一致的问题。
2)log层的设计就是crash_recocery for
 multi-steps updates.

####fs.c
文件系统的实现,5 layers。
blocks log files dirs names.
disk区域为
boot superblock inode bitmap datablock log

#####blocks
[1]
reasdsb:
读取super block 函数

[2]
bzero：
数据块儿设置为0。
memset(bp->data,0,BSIZE)
log_write(bp)

[3]
balloc:
分配一个zero的block,在map里标记已经in use了。

[4]
bfree函数
释放一个bloclk，其实就是改map。

总结：除了logwrite，其它都是调用logwrite，而不是直接调用bwrite。
#####inodes
```
struct {
struct spinlock lock;
struct inode inode[NINODE];
} icache;

// On-disk inode structure
struct dinode {
  short type;     // File type
  short major;    // Major device number (T_DEV only)
  short minor;    // Minor device number (T_DEV only)
  short nlink;    // Number of links to inode 
  uint size;      // Size of file (bytes)
  uint addrs[NDIRECT+1];   // Data block addresses
};

// in-memory copy of an inode
struct inode {
  uint dev;           // Device number
  uint inum;          // Inode number
  int ref;            // Reference count
  int flags;          // I_BUSY, I_VALID

  short type;         // copy of disk inode
  short major;
  short minor;
  short nlink;     // count the directories refer to
  uint size;
  uint addrs[NDIRECT+1];
};

```
PS：ref和nlink的区别
ref:是指内存里面有多少指针指向它，没有为0，则不放在内存里面了。
nlink：有多少目录指向inode，为0，则inode直接被free掉。

[1]
alloc:函数
分配一个inode节点。
注意type == 0 是自由的，否则就是分配的。
这不像datablock，没有什么bitmap，他是直接寻找的。

[2]
iupdate：
把内存里面的inode数据更新到disk上。

[3]
iget:函数
iget(uint dev, uint inum)
就是返回一个对应的内存copy，
可能内存里本身就有相应的copy，也可能利用第一个找到的ref为0，不过不会从disk里面读出数据来填充。

[6]
idup函数：
就是把引用ip->ref++加1

[7]
ilock函数:
就把某个inode设置为busy。
并且如果这个数据不是valid，就把数据从硬盘读出来，然后设置为valid

[8]
iunlock(struct inode *ip)函数:
唤醒某个沉睡在ip上的函数

[9]
iput函数:
如果是最后一个则释放掉，如果数据为alid，则更新到disk中。
否则不是最后一个，只是单纯减少1.

[10]
iunlockput函数：
就是先unlock，再进行iput.

#####inode content
那些data block都存放在ip->addrs[]

[1]
bmap函数:
如果有，就直接返回地址。
如果没有，就申请一个，还有看你是直接地址还是简介地址。

[2]
itrunc函数：
把这inode对应的data block都释放掉。

[3]
stati函数：
把ip的info拷贝到st着中去。

[4]
readi:redi(ip,char *dst,unit off,uint n)
从inode中读出数据来

[5]
writei:
把数据写到inode的data block中去。
然后把内存的inode更新到disk上去。

#####direcrotyies

```
#define T_DIR  1   // Directory
#define T_FILE 2   // File
#define T_DEV  3   // Device
```
[1]
namecmp函数:比较名字是否相同
相同返回0

[2]
drilookup：
struct indoe * dirlookup(strict inode *dp,char *name,unit *poff)
就是超找目录，如果查找到了，使poff设为入口返回。

[3]
dirlink:
int dirlink(struct inode *dp, char *name, uint inum)
Write a new directory entry (name, inum) into the directory dp.
把新目录写进去。

