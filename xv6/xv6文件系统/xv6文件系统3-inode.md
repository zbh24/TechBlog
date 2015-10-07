####Block allocator
[1]
bitmap决定哪些那些块儿是空闲和使用的。
[2]
balloc和bfree来分配块儿
PS：写都是写到日志块儿，读呢，是读buffer_cache？？？
不是，具体情况具体分析，要是superblock，就直接通过buffer_cache来读取，因为它不会去修改。其它的，写都是通过log_write,那么读取呢？？？？

####inodes
inodes在这里有两个概念，一是指文件的属性和指向一系列的data blocks，二是指在buffer_cache里面的inode。
[1]
```
struct dinode {
short type;	// File type
short major; 
short minor;
short nlink; //Numbers of links
uint size; // File size
uint addrs[NDIRECT+1]; //record the blocks numbers
};
```
内核会保留一系列活跃的内核拷贝在内存里面，如：
```
// in−memory copy of an inode
struct inode {
	uint dev; // Device number
	uint inum; // Inode number
	int ref; // Reference count
	int flags; // I_BUSY, I_VALID
	
	short type; // copy of disk inode
	short major;
	short minor;
	short nlink;
	uint size;
	uint addrs[NDIRECT+1];
};
```
是否保存inode在内存里，要看ref，引用计数，通过两个函数去操作。iget函数和iput函数。ilock函数和iunlock函数

[2]
code:
首先分配inode,通过函数ialloc函数,分配成功，改写inode，写回磁盘。
```
// Allocate a new inode with the given type on device dev.
// A free inode has a type of zero.
struct inode*
ialloc(uint dev, short type)
{
	int inum;
	struct buf *bp;
	struct dinode *dip;
	struct superblock sb;
	readsb(dev, &sb);
	for(inum = 1; inum < sb.ninodes; inum++){
		bp = bread(dev, IBLOCK(inum));
		dip = (struct dinode*)bp−>data + inum%IPB;
		if(dip−>type == 0){ // a free inode
			memset(dip, 0, sizeof(*dip));
			dip−>type = type;
			log_write(bp); // mark it allocated on the disk
			brelse(bp);
			return iget(dev, inum);
		}
		brelse(bp);
	}
	panic("ialloc: no inodes");
}

// Find the inode with number inum on device dev
// and return the in−memory copy. Does not lock
// the inode and does not read it from disk.
static struct inode*
iget(uint dev, uint inum)
{
	struct inode *ip, *empty;
	acquire(&icache.lock);
	// Is the inode already cached?
	empty = 0;
	for(ip = &icache.inode[0]; ip < &icache.inode[NINODE]; ip++){
		if(ip−>ref > 0 && ip−>dev == dev && ip−>inum == inum) {
			ip−>ref++;
			release(&icache.lock);
			return ip;
		}
		if(empty == 0 && ip−>ref == 0)
			// Remember empty slot.
			empty = ip;
	}
	// Recycle an inode cache entry.
	if(empty == 0)
		panic("iget: no inodes");
	ip = empty;
	ip−>dev = dev;
	ip−>inum = inum;
	ip−>ref = 1;
	ip−>flags = 0;
	release(&icache.lock);
	return ip;
}
```
记住，iget只是得到一个缓冲区，既没有写，也没有把这个锁住。
如果要写或者读，需要申请锁住。
```
/ Lock the given inode.
// Reads the inode from disk if necessary.
void
ilock(struct inode *ip)
{
	struct buf *bp;
	struct dinode *dip;
	if(ip == 0 || ip−>ref < 1)
		panic("ilock");
	acquire(&icache.lock);
	while(ip−>flags & I_BUSY)
		sleep(ip, &icache.lock);
	ip−>flags |= I_BUSY;
	release(&icache.lock);
	
	if(!(ip−>flags & I_VALID)){
		bp = bread(ip−>dev, IBLOCK(ip−>inum));
		dip = (struct dinode*)bp−>data + ip−>inum%IPB;
		ip−>type = dip−>type;
		ip−>major = dip−>major;
		ip−>minor = dip−>minor;
		ip−>nlink = dip−>nlink;
		ip−>size = dip−>size;
		memmove(ip−>addrs, dip−>addrs, sizeof(ip−>addrs));
		brelse(bp);
		ip−>flags |= I_VALID;
		if(ip−>type == 0)
			panic("ilock: no type");
	}
}
```

