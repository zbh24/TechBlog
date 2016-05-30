# C++相关概念   

标签（空格分隔）： 未分类

---

1.函数模板
就是为了实现代码重用，即是所谓的参数化多态。
```
template <class T>
或者template <typename T>
```

下面来展示一个例子
```
template <typename T>
T abs(T X) {
    return x;
}

int main() {
    int n = abs(5);
    double m = abs(5.0);
}
```

函数模板跟重载是密切相关的，而且都是基本类型。

2.类模板就是这样
template <模板参数表>
class 类名
{
类成员声明
}
下面来展示一个例子
```
template <class T>
class Store{
    private:
        T item;
        int haveValue;
    public:
        Stroe(void);
        T GetElem(void);
        void PutElem(T X);
};

//类外实现
template<class T>
T Store<T> ::GetElem(void) {
    
}

template<class T>
void Store<T> ::PutElam(T x) {
}

int main() {
    Store <int> S1;
    Store <Student> S2;
}
```
3.我们可以泛型一些常用的数据结构。
Array:相对于数组来说，具有可扩展，且不会越界的特点。
List:
Stack:
Queue:

4.STL:标准模板库，是面向对象和泛型程序设计的典范。
泛型：首先是标准容器，然后是标准算法。

迭代器就是算法和容器之间的接口
标准模板库是标准程序库的核心，STL最关键的有容器，迭代器，算法，和函数对象。C语言的那些函数，依然在C语言头文件声明中如 string.h 改成 cstring
1)向量，列表，双端队列Vector list deque
2)集合 set，映射 map
3)栈，队列 stack queue
4)算法 algorithm
5)迭代器 iterator
6)函数对象就在 functional

几个概念：
容器 适配器（就是接口） 迭代器（就是指针）  算法

顺序容器：向量 列表 双端队列
关联容器：集合 映射

1）对于顺序容器：
必须有以下
插入：push_front push_back insert =
删除：erase
访问：fornt back []
2)适配器

3）迭代器

5.流的概念
就像C语言一样，本身并没有提供输入输出语句。其它都是文件，抽象成文件。

6.操作数重载
