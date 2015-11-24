#xv6file system
我在bio.c里面加了一个
b->flags = 0

一.
- LOGZIE = （MAXOPBLOCKS *3）
- MAXOPBLOCKS = 10
- NINOODES 200


所以log的头最多可以记录30个数据块儿

二.
disk layout:
boot block | sb block | log | inode blocks | free bit map | data blocks

nmeta 等于是除了data blocks的数量
nblocks = FSSIZE - nmeta: data blocks的数量
FSSIZE = 1000：就是1000个blocks

ROOTINO = 1 ,就是rootino的起始号是从1开始的

**#define IBLOCK(i, sb)     ((i) / IPB + sb.inodestart)**
既然inode没有bit map，那怎么分配呢。ialloc num
其实是挨个寻找的，只要是type == 0，那么就认为这个没有用，我们可以使用。

mkfs fs.img files

分配一个inode节点，一个inode节点是没有名字的。
有个疑问：/是怎么创建的


