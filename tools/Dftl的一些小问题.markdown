# Dftl的一些小问题

标签（空格分隔）：dftl算法设计

---
###Dftl replacement algorithm
DFTL uses the on-flash limited SRAM to store the most popular (specifically, most recently used) mappings while the rest are maintained on the flash device itself. The core idea of DFTL is easily seen as inspired by the intuition behind the Translation Lookaside Buffer (TLB) [10].

We use the segmented LRU array cache algorithm [18] for replacement in our implementation. However, other algorithms such as evicting Least Frequently Used mappings can also be used.

###Three cache disguaduing algotithms
Finally, we investigate the performance of three cache replacement algorithms: random replacement (RR),
least recently used (LRU), and a frequency-based variation of LRU known as segmented LRU (SLRU).

- Random replacement (RR): This algorithm replaces cache lines by randomly selecting a cache line to discard. This policy is the easiest to implement but generally performs poorly, especially for small cache sizes, because it does not make use of the attributes of spatial and temporal locality that are associated with U0 request patterns. 

- Least recently used (LRU): The LRU algorithm is one of the most popular replacement policies, particularly in commercial implementations. It is used widely in database buffer management, virtual-memory management, file system and I/O caches. This policy exploits the principle of temporal locality and evicts the cache line used least in the recent past on the assumption that it won’t be used in the near future. It is simple to implement for small caches but becomes computationally expensive for large ones. In addition,LRU uses only the time since last access and does not take into account the access frequency of lines when making replacement decisions. 

- Least frequently used (LFU): This algorithm uses the history of accesses to predict the probability of a subsequent reference. The cache maintains a frequency-of-access count for all its lines and replaces the line that has been used least frequently. Unfortunately, lines with large frequency counts that
will not be accessed again (such as a recently active but currently cold file) tend to remain entrenched in the cache,preventing newer additions to the cache from gathering sufficient reference counts to stay in the cache. This leads to a phenomenon called cache pollution, in which inactive data tends to increase the miss rate and hence reduce the performance of the cache. Generally, an aging policy is used to
increase the performance of LFU, by which the frequency counts of inactive cache lines are gradually reduced, making them candidates for replacement. 

- Variations on LRU A frequency based LRU replacement algorithm4 improves on LRU by partitioning the
LRU stack into three sections whose sizes are tunable. On being referenced,a line is placed in the topmost section of the stack. Unlike LFU, the reference count of lines repeatedly referenced in
the top section is not incremented. Thus, temporary “locality of reference” is factored out. Eventually, the line ages into the bottom part of the list by LRU replacement and is finally evicted
if not referenced.An interesting and sophisticated LRU K-page-replacement algorithm5 for database page buffering could also find possible use in I/O caches. For each page, this algorithm maintains a history
table that contains the times of the last K references, factoring out correlated references due to temporary locality as in frequency-based replacement, The cache is implemented as an LRU list,and the decision as to which cache line to replace is based on the history table and other access pattern parameters.

Segmented LRU (SLRU)
An SLRU cache is divided into two segments, a probationary segment and a protected segment. Lines in each segment are ordered from the most to the least recently accessed. Data from misses is added to the cache at the most recently accessed end of the probationary segment. Hits are removed from wherever they currently reside and added to the most recently accessed end of the protected segment. Lines in the protected segment have thus been accessed at least twice. The protected segment is finite, so migration of a line from the probationary segment to the protected segment may force the migration of the LRU line in the protected segment to the most recently used (MRU) end of the probationary segment, giving this line another chance to be accessed before being replaced. The size limit on the protected segment is an SLRU parameter that varies according to the I/O workload patterns. Whenever data must be discarded from the cache, lines are obtained from the LRU end of the probationary segment.[9]"

###总结一下
几种cache替换算法。
- 随机替换（random replace)
- 最少最近使用（Least recently used)
- 最少频繁使用(Least frenquency used)
- segment LRU(把整个lru分成两个区，一个保护区，一个暂时区。在保护区里访问只会移动到保护区顶端，不会增加频率.所以，在保护区里面频率都是访问两次的)
