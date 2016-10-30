# Java并发

标签（空格分隔）： 未分类

---
###Java并发基础知识
1.在Java中线程状态切换方法也有类似POSXI这几种：
1）create是生成类就会生成
2）start方法是线程开始就绪，等待运行。
3）join是等待其它线程结束
4）yield是放弃线程运行时间
5）setProity是设置优先级的方法，一共10级
6）sleep方法是沉睡
7）interrupt方法，中断线程。被中断后，要发出中断异常，关于中断异常，不仅，interrupt，Join和sleep也会发出。这里中断相当于是一个状态，还有一个检测方法是否是中断状态，interrupted().调用中断方法一般是发生死锁，强行恢复。

PS：sleep和yield并不会释放锁，还有两个方法wait和notify这是继承自Object

2.同步方法
1)synchronized是内置锁

3.wait和notofy方法只有类支持多线程时才有用，
1）notify只是随机选择一个阻塞变为可执行，notifyall是选择所有
2）wati将会释放锁

4.多线程使用的方法
1)在Main线程里面，crate几个线程来做不同的事情。这种情况，把线程创造完成以后，可以等待几个线程结束，这种情况都不需要用到同步，比较简单。
```
t1.join();
t2.join();
```
最新的，推荐使用方法
```
CountDownLatch count = new CountDownLatch(3);  
count.await(15,TimeUnit.MINUTES);
//在实现线程的时候，注意需要，要在run里面执行
this.count.countDown();
```
2)第二种，在一个类里面，可以多个方法，比如加和减，现在，可能同时操作，这个时候，就需要了。
1.比如一个类的类变量，所有对象共享，当然可以多线程去做。
2.现在是一个对象的私有变量，可不可以用两个线程去运行，个目前没有想清楚怎么去做，当然可以做。

###JDK1.5以后
分为三个包：
```
conncurrnt
Atomic
Lock：可重入锁（ReetranstLock)
```
1.Executor:
1）为什么要用executor,因为让它来帮你管理线程，这样就方便多了。
线程池里面，找出一个线程出来。
```
ExecutorService exec = Executors.newCachedThreadPool();
exec.execute(new ObjectImplemntsRunnabne());

exec.shutdown();
```
有newCachedThreadPool和FixedThreadPool等等。
newCachedThreadPool:创建了一个根据需要线程大小的线程池，但是以前的可用时会复用。
fixedThreadPool:创建了一个固定数量大小的线程池，但是这里面的线程都是可以复用的。假如你要做10个任务，只创建了new fixedThreadPool(5)个，那么要等待了。

2）Calledable接口
为什么不用从Runable接口，有任务中返回值，需要实现call方法
用submit方法提交

2.共享访问
1）synchronized:
所有的对象都自动含有锁（监视器），当在对象上使用这个方法，就加上锁了。
每个类也有锁，所以synchronized可以用在static方法上

2）新实现JAVA 5
Lock对象，显示的锁。
```
Lock lock = new ReetrantLock()
lock.lock()
// do something
lock.unlock()
```
不过，一般用老式的就够了，只有特殊时才需要使用，可以更细小的控制粒度，尝试锁失败了可以去做点别的事情。

3）原子性和易变性
不要以为原子操作不可中断，就不需要同步。
最好的变法还是用同步。

4）原子类
AtomicIngeter，AtomicLong，AtomicBool
都是compare and set这是依赖于机器的原子性操作。

5)在对象上进行同步，比如
synchronized(this)

3.线程状态
1）进入阻塞的条件： sleep，wait，或者因为锁卡住了。
2）这个没懂

4.线程之间的协作
wait和notify对象
await()和signal()方法的condtional对象
1）因为wati会释放锁，所以只能在同步块里面使用，调用时释放锁。当wait被唤醒后，必须重新获得锁，才能运行。
2）JSE 5
```
Lock lock = new ReetrantLock()
Condtion condtion = lock.newCondtion()
...
condtion.signalAll()
condtion.await()
```
3）更高级的解决任务互斥，同步队列,BlockingQueue
```
 class Producer implements Runnable {
   private final BlockingQueue queue;
   Producer(BlockingQueue q) { queue = q; }
   public void run() {
     try {
       while (true) { queue.put(produce()); }
     } catch (InterruptedException ex) { ... handle ...}
   }
   Object produce() { ... }
 }

 class Consumer implements Runnable {
   private final BlockingQueue queue;
   Consumer(BlockingQueue q) { queue = q; }
   public void run() {
     try {
       while (true) { consume(queue.take()); }
     } catch (InterruptedException ex) { ... handle ...}
   }
   void consume(Object x) { ... }
 }

 class Setup {
   void main() {
     BlockingQueue q = new SomeQueueImplementation();
     Producer p = new Producer(q);
     Consumer c1 = new Consumer(q);
     Consumer c2 = new Consumer(q);
     new Thread(p).start();
     new Thread(c1).start();
     new Thread(c2).start();
   }
 }
```
总结一下，你像管道基本上就是一个阻塞队列啊。

5.死锁
哲学家的问题

6.新类库的其他构件
1）CountDownLatch：
同步n个任务，创建完成以后await，然后其他每个线程任务完成以后，调用countDown(),来减少1。
任务分解
2）CyClicBarrier：多次的CountDownLatch
3）DelayQueue:
4)PeiortyBockingQueue:优先级的队列
5）semaphore：信号量，可以有多个,用来控制线程的进出控制了。
A counting semaphore. Conceptually, a semaphore maintains a set of permits. Each acquire() blocks if necessary until a permit is available, and then takes it. Each release() adds a permit, potentially releasing a blocking acquirer. However, no actual permit objects are used; the Semaphore just keeps a count of the number available and acts accordingly.
6）Exchanger:

7.性能调优和比较各类互斥技术
1）synchronized lock atomic
大规模时能使用这个atomic最好了，其次是lock，最后才是synchronized
2)免锁容器
CopyOnWriteArrayList这样保证多个读是可以的，并不需要加锁的。

ConcurrentHashMap和ConcurrentLinkedQueue
乐观锁：
乐观加锁：
3）ReadWriteLock：
这个对数据结构相对不频繁写入，但是，有多个任务经常要读取的经行了优化。


---------------------------------------
1.对象里面可以有自己，
这就相当与struct里面有自己的引用。
```
struct x{
struct x* next;
}
```

2.工厂模式和适配器模式，单例模式。

3.
1)xchg
2)test and set(TSL)
大家做法都类似。
```
进入时：
spin_lock:
move eax 1
xchg eax ,lock
cmp eax 0
JNE spin_lock
ret

退出时：
move 0,eax
ret
```
3)compare and set
JAVA里面是用这个保证原子性的

4)compare and swap

5）Future

-----------------------------------
1.vector和hashtab本事是可以多线程的

2.多线程的内存模型：main memory（主存）、working memory（线程栈），在处理数据时，线程会把值从主存load到本地栈，完成操作后再save回去(volatile关键词的作用：每次针对该变量的操作都激发一次load and save)。

3.future模式：并发模式的一种，可以有两种形式，即无阻塞和阻塞，分别是isDone和get。其中Future对象用来存放该线程的返回值以及状态。

它是这样的，做完任务以后，可以不阻塞，去进行其他计算，直到调用 future.get()任务，去进行阻塞。