# JAVA容器简单理解

标签（空格分隔）： 未分类

---

1.JAVA容器
主要分类：Collection接口和Map接口
```
Collection
├List
│├LinkedList
│├ArrayList
│└Vector
│└Stack
└Set
Map
├Hashtable
├HashMap
└WeakHashMap
```
Collection有以下：
```
1）
ArrayList和LinkedList，线程安全的ArrayList有Vector.
然后Stack是继承自Vector，是线程安全的。Queue接口

2）Set有HashSet和TreeSet
```
```
Map接口
下面实现了HahsMap（线程不安全，用HashTable实现的）和TreeMap，有安全版本的ConcurrentHashMap
然后有HahsTable：这是线程安全的
HashMap x = new HashMap<K,V>();

Hashtable numbers = new Hashtable();
　　　　numbers.put(“one”, new Integer(1));
　　　　numbers.put(“two”, new Integer(2));
　　　　numbers.put(“three”, new Integer(3));
　　要取出一个数，比如2，用相应的key：
　　　　Integer n = (Integer)numbers.get(“two”);

Hashtable 通过initial capacity和load factor两个参数调整性能。通常缺省的load factor 0.75较好地实现了时间和空间的均衡。增大load factor可以节省空间但相应的查

由于作为key的对象将通过计算其散列函数来确定与之对应的value的位置，因此任何作为key的对象都必须实现hashCode和equals方 法。

```
2.简单泛性容器对象
1）
```
List Set Queue Map
```
比如说Set有HashSet和TreeSet和LinkedHashSet
迭代器访问时
HashMap：查找结果比较快，没有明显顺序保存键。
TreeMap：按照升序的结果来保存键
LinkedHashMap:访问速度和HashSet一样快，按照插入顺序保存键。

TreeSet就是用TreeMap实现的，而TreeMap是用红黑树来实现的。
LinkedHashSet也使用了Hash，但是它额外使用了一个链表来维护插入的顺序。

2）Queue
PriorityQueue:优先级的队列。这个是怎么实现的。？？？？实现comparable
offer
poll
优先级别是通过使用comparator来定义的。
```
vector Stack Hashtable是过时的，不应该使用去，恰好这几个是线程安全的。
LinkedList 提供了实现Stack和Queue的所有方法

```

3.JAVA SE5以后

- 新的Queue，PriorityQueue ，各种风格的BlockingQueue
- ConcuurentHashMap
- CopyOnWriteArrayList CopyWriteArraySet
1)对于HashSet，TreeSet，LinkedSet，第一个和第三个必须实现hashCode和equals，第二个必须实现compareto接口。
2）HashMap，TreeMap，LinkedHashMap()，或者插入顺序，最近最少未使用
3）CopyOnWriteArray:使用copyonwritre技术，对于读没有锁，对于写加了锁，那么如何防止一个读，一个写呢。
写的时候，写一个副本，最后用原子操作赋值替换掉原来的值，就是这么做的。
这个策略确保了：不会读到中间状态，要么完成，要么没完成。
免锁容器：读没加锁，写加锁了，然后使用了copyOnWrire技术。

还有一种Collectionss.synchroiztions
-------------------------------------、
1.默认的HashCode是地址值，而equals是地址值。
会用equals判断是否键值想等，而用hashcode生成的地址值来散列  `哈希原始值。

2.
load:get 
store:set

3.
对于String来说
==:是地址值想等
equals:是判断值是否想等

-------------------------------------------
###Java垃圾回收
1） 在Young Generation中，有一个叫Eden Space的空间，主要是用来存放新生的对象，还有两个Survivor Spaces（from、to），它们的大小总是一样，它们用来存放每次垃圾回收后存活下来的对象。
2） 在Old Generation中，主要存放应用程序中生命周期长的内存对象。
3） 在Young Generation块中，垃圾回收一般用Copying的算法，速度快。每次GC的时候，存活下来的对象首先由Eden拷贝到某个SurvivorSpace，当Survivor Space空间满了后，剩下的live对象就被直接拷贝到OldGeneration中去。因此，每次GC后，Eden内存块会被清空。
4） 在Old Generation块中，垃圾回收一般用mark-compact的算法，速度慢些，但减少内存要求。
5） 垃圾回收分多级，0级为全部(Full)的垃圾回收，会回收OLD段中的垃圾；1级或以上为部分垃圾回收，只会回收Young中的垃圾，内存溢出通常发生于OLD段或Perm段垃圾回收后，仍然无内存空间容纳新的Java对象的情况。

###Java设计模式
1.迭代器模式：
1）Iterator接口
2）容器类，里面暴露实现了Iterator接口，
3）然后在这个容器类内部定义了一个内部类，这个内部类实现了这个迭代器接口

当然也可以分为四个部分，就是这个容器类也抽象成接口，这是面向接口编程。
拿Java里面的容器来举例来说，也是四个类List ArrayList Iterator Itr两个接口和两个类
形式化定义，下面四个角色：
　　1) 迭代器角色（Iterator）：迭代器角色负责定义访问和遍历元素的接口。

　　2) 具体迭代器角色（Concrete Iterator）：具体迭代器角色要实现迭代器接口，并要记录遍历中的当前位置。

　　3) 容器角色（Container）：容器角色负责提供创建具体迭代器角色的接口。

　　4) 具体容器角色（Concrete Container）：具体容器角色实现创建具体迭代器角色的接口——这个具体迭代器角色于该容器的结构相关。

2.单例模式
Singleton
```
class Single1 {
	
	public volatile static Single1 instance;
	
	public static Single1 getSingle() {
		if (instance == null) {
			synchronized(Single1.class) {
				if (instance == null)
				instance = new Single1();
			}
		}
		return instance;
	}

	private Single1() {}
}
```