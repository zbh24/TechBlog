#xv6文件系统

###overall
xv6文件系统有四大主要特点：
* 记录和管理数据
* crash恢复，通过log
* 不同进程同时操作，保持数据一致性
* 内存cache，频繁访问的存放在内存

软件层分为六层，从最底层到最高层为：
- bloks：（block cache）只能顺序访问，保证每次只有一个程序来访问物理块
- trans（logging）：打包里几个更新的块一起操作，原子操作，要么全部作，要么不做。
- files（不同的inodes和data blocks）：操作文件
- dirctory：目录inode
- pathnames;就是路径，目录树，来查询操作，知道文件
- system calls：文件描述符，抽象了接口给外界，比如管道，设备，文件。

硬件层：
把disk分为
- 0：第0块儿是boot
- 1：第1块儿是suprerbloc，记录这个文件系统有多少inodes，data blocks， log data。
- 2：从第二块儿开始记录inodes，一个block有多个inode
- bitmaps:哪些数据块儿是空闲
- 然后是data blocks，记录数据
- log：最后是log块儿,是transaction一部分

####6层-buffer cache layer
code：bio.c
[1]
两个目标：
* 保证只有一份copy在内存里面，只允许一个线程去访问
* 频繁访问的保存在内存里面

提供两个主要的接口：bread，bwrite
bread：操作buffer，可以在内存里面读或者修改block（这个内存就是指这个buffer）
bwrite：把某个缓冲的buffer写道disk里面
PS：如果要释放这个buffer，就必须调用brelse

原理就是上面，实际上xv6有多个buffer，当一个block的引用的buffer没有释放，再访问这个buffer将会等待。回收buffer的算为最近最近未使用。

[2]
文件定义（fs.h）的头文件，主要包括超级块儿，inode和文件的stat
```
struct superblock {
uint size;
uint nblocks;
uint ninodes;
uint nlog;
};
struct dinode {
short type;
short major;
short minor;
short nlink;
uint size;
uint addrs[NDIRECT+1];
};
//stat用在哪儿
struct stat {
short type;
int dev;
uint ino;
short nlink;
uint size;
};
```
buffercache是个双向链表,所有访问buffercache通过的是bcache.head
```
struct {
struct spinlock lock;
struct buf buf[NBUF];
// Linked list of all buffers, through prev/next.
// head.next is most recently used.
struct buf head;
} bcache;

// Create linked list of buffers
bcache.head.prev = &bcache.head;
bcache.head.next = &bcache.head;
for(b = bcache.buf; b < bcache.buf+NBUF; b++){
b−>next = bcache.head.next;
b−>prev = &bcache.head;
b−>dev = −1;
bcache.head.next−>prev = b;
bcache.head.next = b;
}
```
每个cache有三个状态位，不是3种状态：valid,dirty,basy.
- valid：这个block可以用
- dirty：修改过了，需要写回去。访问时不关心，回收时关心
- busy: 有人访问，还没释放，需要等待。

bread:给定扇区，返回一个buffer
```
struct buf*
bread(uint dev, uint sector)
{
struct buf *b;
b = bget(dev, sector);
if(!(b−>flags & B_VALID))
iderw(b);
return b;
}
```
bget:
```
static struct buf*
bget(uint dev, uint sector)
{
struct buf *b;
acquire(&bcache.lock);
loop:
// Is the sector already cached?
for(b = bcache.head.next; b != &bcache.head; b = b−>next){
	if(b−>dev == dev && b−>sector == sector){
		if(!(b−>flags & B_BUSY)){
			b−>flags |= B_BUSY;
			release(&bcache.lock);
			return b;
		}
		sleep(b, &bcache.lock);
		goto loop;
	}
}
// Not cached; recycle some non−busy and clean buffer.
for(b = bcache.head.prev; b != &bcache.head; b = b−>prev){
		if((b−>flags & B_BUSY) == 0 && (b−>flags & B_DIRTY) == 0){
		b−>dev = dev;
		b−>sector = sector;
		b−>flags = B_BUSY;
		release(&bcache.lock);
		return b;
	}
}
panic("bget: no buffers");
}
```
bread：如果调用者调用bread得到一个buffer，那么就可以读或者写了。如果写了，那么在释放brelase之前，必须调用bwrite写到磁盘里面。
bwrite：
```
// Write b’s contents to disk. Must be B_BUSY.
void
bwrite(struct buf *b)
{
if((b−>flags & B_BUSY) == 0)
	panic("bwrite");
b−>flags |= B_DIRTY;
iderw(b);
}
// Release a B_BUSY buffer.
// Move to the head of the MRU list.
void
brelse(struct buf *b)
{
if((b−>flags & B_BUSY) == 0)
	panic("brelse");
acquire(&bcache.lock);
b−>next−>prev = b−>prev;
b−>prev−>next = b−>next;
b−>next = bcache.head.next;
b−>prev = &bcache.head;
bcache.head.next−>prev = b;
bcache.head.next = b;
b−>flags &= ~B_BUSY;
wakeup(b);
release(&bcache.lock);
}
```

**总结**：这层通过提供两个主要的接口，保证了可以对block的读写，而且只有一份拷贝在内存里，且只有一个线程可以读。

