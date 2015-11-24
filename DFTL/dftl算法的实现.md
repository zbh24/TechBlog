#关于dftl的实现

####关于模拟
我实现的，定义的是模拟整个数据块，不然就是对整个disk做缓存，显然不会这么做了。


####定义数据结构
那些实际的数据都要用结构体struct定义成实际的，因为是连续的，可以用连续的数组表示。

对于其它的，比如当前的数据块和映射块，可以用指针来表示

####关于写数据
对于一整块的数据，可以依次来强制转换，这样结构体就对齐了，这样每次，再前进一个结构体的偏移。
```
for(inum = 1; inum < sb.ninodes; inum++){
     bp = bread(dev, IBLOCK(inum, sb));
     dip = (struct dinode*)bp->data + inum%IPB;
     if(dip->type == 0)  {  // a free inode
        memset(dip, 0, sizeof(*dip));
        dip->type = type;
        log_write(bp);// mark it allocated on the disk
        brelse(bp);
        return iget(dev, inum);
      }
         brelse(bp);
   }
```
