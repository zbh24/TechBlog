#Nand的算法

**为什么要有FTL软件**？？？？
因为原来如果有冲突，就要其它数据拷贝走，然后擦除那个块，再挨个写回去。这样冲突多，会擦除特别多。
因为擦除特别消耗时间，为了解决这个问题，我们增加了一个FTL层。
FTL主要目标是：保证每次写都是往空的去写。

FTL：是地址转换表，我们要做的也就是实现这个ftl算法。上层给我们一个虚拟地址，我们需要去找到一个物理地址。
**FTL算法：**
1）lbn = lsn/4
2）offset = lsn mod 4
3）通过bmp表，找到lbn对应的pbn
4）去写pbn,offset
5）如果冲突，就分配一个free block，然后把其它拷贝过来，这就是merge。更改bmp，然后回收擦除旧的块儿。

提出了很多FTL算法，其中log算法表现出色。
log算法：就是如果有冲突，就往log日志块的空的区域去写。有效减少了擦除次数。
一个新的好的FTL算法BAST

PS：GC就是合并以后，原来的数据块儿没有用了，需要擦除回收，这就是GC。

##BAST
其它，都很像，唯一不同的是它会写到log块儿。
有两个表，一个日志块儿表，一个是log表。
- block mapping table
lbn pbn
- log表
lbn pbn lsns
1    20   {4,4,6,7}
这就是BAST算法，增加了一组log块儿，而且这些log块儿是组相联的，也就是这个log块儿都对应于某个数据块儿块儿。

可以认为data block是block-level，而log是sector-level的。
通常这些映射表是放在 SRAM里面。

Merge:有这几种，
1）switch：直接交换
2）合并，merge



##FAST
它与BAST的区别
它的log块儿算法。日志块儿分两种。一种是顺序读，组相联。一种是随机写，全相联。

所以，现在大部分FTL的策略是：
data block：是block—level
log block：是sector—level,然后分为全相连还是组相连

##DFTL
解决了大规模的随机写。英文原文：The poor performance of random writes has been a cause of major concern which needs to be addressed to better utilize the potential of flash in enterprise-scale environments.
也就是避免了full merge。

主要贡献：
1）在于是完全的page映射。
2）把一些popular的放到了flash的	SRAM里面，然后剩余的放到了falsh里面，类似TLB。利用程序的局部性。

1）OOB：有逻辑lsn，然后还有state
2）完全的page-mapping，然后连续存在在flah上，然后区别data area和translation area，也就是与有两种page：data page和translation page
3）CMT GTD
4）
- 地址匹配算法，Address Translation
- 垃圾回收算法，Garbage Collection

5）另外两个block：current data block和current translation block。
- 读：那个算法1，地址转换完成就可以读了。
- 写和更新是一样的：直接写current data block，然后更新CMT，这是个lazy算法。
- GC：分两种块儿。：
- 如果是translation black，那么就直接拷贝到current translation block，然后更心不甘GTD。
- 如果是data blck，我们只更新CMT。

##other
1）为什么要有逻辑地址到物理地址的映射？
内存里面有，一个是因为文件很大，一下子不能拿进来，所以这样就可以拿需要执行的部分。
flash要有映射的目的跟计算机要有内存不一样。

2）以BAST为例子，当没有free log或这个log写满时，有三种GC策略（merge）：
- switch 
- partil merge
- full merge 

full merge消耗时间最多，至少要擦除两个，当是FAST算法时，擦除次数可能非常多。
