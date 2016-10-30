#Java面试常问题目

标签（空格分隔）： 未分类

---

一.java基础
1.HashMap的实现原理
它是由一个数组组成的，这个数组的每个元素是链接节点。所以，他hash冲突的时候，就会插入这个链表的头节点中。
key为空也可以插入。
注意：这个HashMah哈希冲突的时候，只有equals不同，才可以插入链接，否则就直接覆盖了。
比如：
ha.push(1,"abc")
ha.push(1."ss")
就覆盖了。

对于使用了hashmap的类，一定要实hashcode和equals。

2.反射

3.Java内存泄漏定位

4.异常的结构
Exception有：
RuntimeException：这是unchecked 异常，这里空指针，数组越界。
IOexception：这是checked 异常。

5.Java的引用类型
强引用 软引用 弱引用 虚引用

6.Hash冲突怎么办，有哪些解决冲突的办法。
1）线性冲突再散列
2）二次再散列
3）链式法

7.hashcode的生成与equals的生成算法。
对于hashmap来说，他的hash是利用原来的元素的hashcode的算法来生成地址的。
举个例子，对于string，他是用每个字符的值×31+这个字符值的来计算的。他的equals就是比较字符串字面值是否想等。
那么HashMap的算法是利用它的hashcode于hashcode由移16位然后异或。

二.jVM
1.JAVA的内存模型
堆：分为年代代和老年代，年代代分为（ed，surv from，surv to）
栈：局部变量表，操作数栈，动态链接，返回地址
方法区：
本地方法栈：
程序计数器：

2.JVM性能调优做了什么
堆空间大小的划分。
带CMS参数的都是和并发回收相关的
-XX:+UseParNewGC，对新生代采用多线程并行回收。
CMSInitiatingOccupancyFraction=90说明年老代到90%满的时候开始执行对年老代的并发垃圾回收（CMS）
用jmap和jstack查看


3.JAVA 8
在heap space里面有：minor gc，和full gc，后者开销很大。
永久带：没有了和那个和heap space分开了。
现在这个区域叫做metaspace。

三.多线程
1.用start和直接调用run的区别
用start是开启多线程
而用run是直接调用，并没有使用多线程技术。

2.常用线程池子和场景
newFixedThreadPool:另外如果达到最多怎么办？考察底层基本实现原理，可以一直提交人物，直达最后资源耗尽，因为提交的人物队列为无界的阻塞队列。
public ThreadPoolExecutor()：
newCachedThreadPool：有界阻塞队列，提交超过最大数会拒绝服务。

PS；区别
ArrayBlockingQueue：是一个基于数组结构的有界阻塞队列，此队列按 FIFO（先进先出）原则对元素进行排序。
LinkedBlockingQueue：一个基于链表结构的无界阻塞队列，此队列按FIFO （先进先出） 排序元素，吞吐量通常要高于ArrayBlockingQueue。静态工厂方法Executors.newFixedThreadPool()使用了这个队列。
```
public static ExecutorService newCachedThreadPool() {
        return new ThreadPoolExecutor(0, Integer.MAX_VALUE,
                                      60L, TimeUnit.SECONDS,
                                      new SynchronousQueue<Runnable>());
    }
    
public static ExecutorService newFixedThreadPool(int nThreads, ThreadFactory threadFactory) {
        return new ThreadPoolExecutor(nThreads, nThreads,
                                      0L, TimeUnit.MILLISECONDS,
                                      new LinkedBlockingQueue<Runnable>(),
                                      threadFactory);
    }
```
所以，cachedThreadPool的为有界队列，最大提交任务为Ingeter.maxvalue，而FixedThreadPool为无界队列。

创建线程的步骤是这样的，先创建coresize的线程，现在再来就放到人物队列里面。如果人物队列满了，那么只要小于max，那么就可以继续创建线程，这是针对有界队列的。
newCachedThreadPool
工作队列的默认选项是 SynchronousQueue，它将任务直接提交给线程而不保持它们。在此，如果不存在可用于立即运行任务的线程，则试图把任务加入队列将失败，因此会构造一个新的线程。此策略可以避免在处理可能具有内部依赖性的请求集时出现锁。直接提交通常要求无界 maximumPoolSizes 以避免拒绝新提交的任务。当命令以超过队列所能处理的平均数连续到达时，此策略允许无界线程具有增长的可能性。

对于无界队列的，是一直排队，这个人物队列可以无限大。

3.
reenterantLock：这个更灵活，可以普通锁，时间锁，可中断锁，还提供了condtion来处理这个事情。
sychronized：这个比较使用简单。
```
Class Foo 
{

    public synchronized static void methodAAA()   // 同步的static 函数 
    { 
        //…. 
    }

    public void methodBBB() 
    {

       synchronized(Foo.class)   // class literal(类名称字面常量)

    } 
}
```
这两个是等价的，每一个类和实例都是有锁的。

4.ConcurrentHashMap的实现原理
更令人惊讶的是ConcurrentHashMap的读取并发，因为在读取的大多数时候都没有用到锁定，所以读取操作几乎是完全的并发操作，而写操作锁定的粒度又非常细，比起之前又更加快速（这一点在桶更多时表现得更明显些）。只有在求size等操作时才需要锁定整个表。

JAVA1.8采用了乐观加锁的技术（CAS)。

在1.6里面，它的读是完全并发的，它写是分段锁的，找到对应点的，锁住这里，，复制一份副本，在副本上修改，然后再泳原子替换。
这样就实现了高并发技术。

在1.8里面，它已经不用显示的锁了，而用了CAS技术。

5.什么叫线程安全？
比如说，多个线程执行同一个操作，不会出现意外的结果，不会每一次执行都不一样。

6.BlockingQueue的使用
take与poll的区别：前面操作阻塞
put与offer的区别：：区别就是否阻塞
peek查看队头。

ArrayListBlockingQueue：有界的
LinkedListBlockingQueue:无界的
DelayQueue：无界的PriorityQueue，只有当delay过期了才能take。
ProrityQueue：用堆来实现的，这个是一个堆。(只有这一个是线程不安全的)
PeorityQueueBlockingQueue：线程安全的，不过用堆。

这些队列，对应的还设有DoubleQueue

7.基于I/O多路多用
跟多进程和多线程的区别还是很大的，不需要多进程技术。

四.网络方面
1.TCP/IP三次握手

2.链接淘宝
1）DNS，ip地址
2）TCP三次握手
3）http请求
4）如果是ssl的，用rsa的,Secure Socket Layer.
淘宝把公钥发给我，然后我用公钥来加密。
我们商量一个米钥，然后来做。

GET、POST、HEAD、OPTIONS、PUT、DELETE和TARCE。

3.Socket通信模型
AIO和NIO

4.对称和非对称加密
对称加密：AES，DES。
非对称加密：RSA

5.同步和异步
同步：阻塞
异步：非阻塞

6.http，tcp和udp的区别

五.数据库MYSQL
1.有哪些引擎
1 MyISAM：这种引擎是mysql最早提供的。这种引擎又可以分为静态MyISAM、动态MyISAM 和压缩MyISAM三种：
    静态MyISAM：如果数据表中的各数据列的长度都是预先固定好的，服务器将自动选择这种表类型。因为数据表中每一条记录所占用的空间都是一样的，所以这种表存取和更新的效率非常高。当数据受损时，恢复工作也比较容易做。
    动态MyISAM：如果数据表中出现varchar、xxxtext或xxxBLOB字段时，服务器将自动选择这种表类型。相对于静态MyISAM，这种表存储空间比较小，但由于每条记录的长度不一，所以多次修改数据后，数据表中的数据就可能离散的存储在内存中，进而导致执行效率下降。同时，内存中也可能会出现很多碎片。因此，这种类型的表要经常用optimize table 命令或优化工具来进行碎片整理。
    压缩MyISAM：以上说到的两种类型的表都可以用myisamchk工具压缩。这种类型的表进一步减小了占用的存储，但是这种表压缩之后不能再被修改。另外，因为是压缩数据，所以这种表在读取的时候要先时行解压缩。
    但是，不管是何种MyISAM表，目前它都不支持事务，行级锁和外键约束的功能。
    2 MyISAM Merge引擎：这种类型是MyISAM类型的一种变种。合并表是将几个相同的MyISAM表合并为一个虚表。常应用于日志和数据仓库。
    
    3 InnoDB：InnoDB表类型可以看作是对MyISAM的进一步更新产品，它提供了事务、行级锁机制和外键约束的功能。
    
    4 memory(heap)：这种类型的数据表只存在于内存中。它使用散列索引，所以数据的存取速度非常快。因为是存在于内存中，所以这种类型常应用于临时表中。
    
    5 archive：这种类型只支持select 和 insert语句，而且不支持索引。常应用于日志记录和聚合分析方面。
    当然MySql支持的表类型不止上面几种。

2.数据库事务
数据库事务(DatabaseTransaction)，是指作为单个逻辑工作单元执行的一系列操作，要么完全地执行，要么完全地不执行。
一个逻辑工作单元要成为事务，必须满足所谓的ACID（原子性、一致性、隔离性和持久性）属性。

3.事务隔离的4个级别（Innodb提供）：
在DBMS中，事务保证了一个操作序列可以全部都执行或者全部都不执行（原子性），从一个状态转变到另外一个状态（一致性）。由于事务满足久性。所以一旦事务被提交之后，数据就能够被持久化下来，又因为事务是满足隔离性的，所以，当多个事务同时处理同一个数据的时候，多个事务直接是互不影响的，所以，在多个事务并发操作的过程中，如果控制不好隔离级别，就有可能产生脏读、不可重复读或者幻读等读现象。

·未提交读(Read Uncommitted)：允许脏读，也就是可能读取到其他会话中未提交事务修改的数据

·提交读(Read Committed)：只能读取到已经提交的数据。Oracle等多数数据库默认都是该级别 (不重复读)

·可重复读(Repeated Read)：可重复读。在同一个事务内的查询都是事务开始时刻一致的，InnoDB默认级别。在SQL标准中，该隔离级别消除了不可重复读，但是还存在幻象读

·串行读(Serializable)：完全串行化的读，每次读都需要获得表级共享锁，读写相互都会阻塞

4.详解四个隔离级别
行级共享锁，行级排他锁。
表共享锁，表排他锁。

“读现象”是多个事务并发执行时，在读取数据方面可能碰到的状况。先了解它们有助于理解各隔离级别的含义。其中包括脏读、不可重复读和幻读。

未提交读：事务在读数据的时候并未对数据加锁，务在修改数据的时候只对数据增加行级共享锁。
会有脏读现象。

提交读：
事务在读取数据时，必须先对其加 行级共享锁 ，读完释放。
事务在更新数据时，必须先对其加 行级排他锁 ，知道结束才释放。

可重复读：
事务在读取数据时，必须先对其加 行级共享锁 ，直到事务结束才释放；
事务在更新数据时，必须先对其加 行级排他锁 ，直到事务结束才释放。

可序列化：
事务在读取数据时，必须先对其加 表级共享锁 ，直到事务结束才释放；
事务在更新数据时，必须先对其加 表级排他锁 ，直到事务结束才释放。

5.索引

6.数据库锁
共享锁：又称读锁，事务A对某行加上行共享锁，其他用户可以并发读取数据，但不能修改（因为需要加上拍他锁），但可以再加上共享锁。

排他锁：又称写锁，对事务A加上排他锁之后，则其他事务不能再对A加任何其他类型的锁。

7.乐观锁，悲观锁

8.数据库B+树
MySql的索引是B+树，大多数索引是B-树或者B+树。索引是用来提高数据库速度的一种数据库对象。

当然，众所周知，虽然索引可以提高查询速度，但是它们也会导致数据库系统更新数据的性能下降，因为大部分数据更新需要同时更新索引。

如果，当你建立一个空表时，你建立一个索引，数据库系统为你分配一个索引页。
1）聚集索引：表按照索引的顺序来存储，叶子结点存储了真是的数据行。
一个表只能对应一个聚集索引

2）非聚集索引：表存储顺序与索引顺序无关，对于非聚集索引，指向逻辑指针。

聚集索引的插入与删除操作是比较麻烦的。

非聚集索引：

索引是建立在相应的列上面的。
还有唯一索引，主键索引。

9.总结一下就是脏读，不可重复读，幻读现象。
对于Innodb这种引擎，默认是RR级别的，就是可重复读。
事务A读数据    事物B修改数据
               commit
事务A读数据还是一样的。（可重复读，但是有幻读，因为只对update和delete有用，它只锁住了这些数据，所以不会变动，insert没用）。
COMMIT
这时候再查询，会看到最新结果。

REPEATABLE-READ事务隔离级别，当两个事务同时进行时，其中一个事务修改数据对另一个事务不会造成影响，即使修改的事务已经提交也不会对另一个事务造成影响。

在事务中对某条记录修改，会对记录加上行共享锁，直到事务结束才会释放。

五.设计模式
1.这是饱汉
```
// version 1.5
public class Singleton
{
    private volatile static Singleton singleton = new Singleton();
    private Singleton()  {    }
    public static Singleton getInstance()   {
        return singleton;
    }
}
```

2.
```
public class SingleTon {
    private static class InSingle {
        private static SingleTone s1 = new SingleTon();
    }
    
    private SingleTon() {}
    public static getInstance() {
        return InSingle.s1;
    }
}
```

```
public enum Singleton{
  INSTANCE；
}
    
```
2.工厂方法


六.算法
1.Haffman编码

2.计算一个正整数的平方根

3.两个有序数组的合并

PS：输入与输出，ACM时。


七.并发与性能调优

八.不太懂框架
三大框架用过，分别负责MVC
hIBRATE:对象式数据库
SPRING MVC：这个依赖注入看一下。

九.反射
反射API中提供的动态代理也是非常强大的功能，可以原生实现AOP中 的方法拦截功能。正如英文单词reflection的含义一样，使用反射API的时候就好像在看一个Java类在水中的倒影一样。知道了Java类的内部 结构之后，就可以与它进行交互，包括创建新的对象和调用对象中的方法等。

这种交互方式与直接在源代码中使用的效果是相同的，但是又额外提供了运行时刻的灵活性。使用反射的一个最大的弊端是性能比较差。相同的操作，用反射API所需的时间大概比直接的使用要慢一两个数量级。不过现在的JVM实现中，反射操作的性能已经有了很大的提升。

Java 反射API的第一个主要作用是获取程序在运行时刻的内部结构

十.锁
无锁：使用无锁结构，无非是对发生冲突保有乐观态度，觉得大多数情况下冲突不会发生，一旦发生就采取重来一次的策略。
CAS无锁结构,它很乐观。

悲观锁：就是认为一定会发生冲突，所以只要访问就锁住。

乐观锁：就是认为不会发生冲突，所以不加锁，等发生冲突时，再具体处理。比如读写锁，它认为有很多线程在访问时读比较多，写很少。所以，就不加锁。一旦发生冲突，那么再具体处理。

----------------------------------------------------------------
1.回去看一下：
洗澡
算法题目
明天计划：
上午投简历
带一下C++，看一下C++，问一下將刚,所以可以用STL。
明天下午看一下OS内核。
选择各个行业的职业规划是什么。

-----------------------------------------------------------

-----------------------------------------------------------------
The old memory model allowed for volatile writes to be reordered with nonvolatile reads and writes

But there is more to synchronization than mutual exclusion. Synchronization ensures that memory writes by a thread before or during a synchronized block are made visible in a predictable manner to other threads which synchronize on the same monitor. After we exit a synchronized block, we release the monitor, which has the effect of flushing the cache to main memory, so that writes made by this thread can be visible to other threads. Before we can enter a synchronized block, we acquire the monitor, which has the effect of invalidating the local processor cache so that variables will be reloaded from main memory. We will then be able to see all of the writes made visible by the previous release.

Under the old memory model, accesses to volatile variables could not be reordered with each other, but they could be reordered with nonvolatile variable accesses

Under the new memory model, it is still true that volatile variables cannot be reordered with each other. The difference is that it is now no longer so easy to reorder normal field accesses around them. Writing to a volatile field has the same memory effect as a monitor release, and reading from a volatile field has the same memory effect as a monitor acquire

学会引导面试官
-------------------------------------------------------------------------










