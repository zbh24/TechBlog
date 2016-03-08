# 字符串操作以及C++标准库

标签（空格分隔）： 未分类

-------------------------------------------------
1.
1）
char c[10] = {'a','b','c'};
char c[10] = "abc";
char c[] = "abc"
这都是等价的，可以操作字串。
但是，这个就不是等价的。
char *s = "abc";

2）
初始化：
char s[] =  {'a',0}
char s[] = {'a','\0'}
char s[2] = {'a',0}

ps：数组初始化
int a[10] = {0};
2.
字符串处理：
在cstring头文件中
有一些标准库文件可以来处理
strcat:连接strcat(s,t)
strcpy
strcmp
strlen
strlwr
strupr

3.C++标准库类
PS：string 不是基本类型，
使用string类，需要预先包含string文件，它封装了一系列的属性和相应的操作。
string append(const char *s)
string assign (const char *s)
int length()
void swap(string& str)
int find

还有一些操作符，它自己string类把它重载了。
+：就是链
!=：不相等
==：相等
s[i]：取第i个字符

例如：生成一个新字符串。
string s;

-----------------------------------------------

有点让人困惑的定义：
别名和指针
add(int &a,int &b)
调用时add(x,y)
或者
add(int *a,int *b)
调用时add(&x,&y)

PS：注意这两个&是不同的，一个是声明，一个是取地址符号

----------------------------------------------------
1.c++重载
int add(int x,int y)
float add(float x,float y)

2.内联函数就是编译时直接嵌入到那儿，而不是发生控制转移

3.一般最简单的类定义
方法public，数据成员都私有
```‵
class Clock
{
public:
    void setTime(int x);
    void showTime();
private:
    int hour,minute,second
};
//注意实现可以在类外做

void Clock::setTime(int x) {
    xxx;
}
```

Clock newClock;
构造函数和析构函数
拷贝构造函数：如果不声明的话，系统会默认生成一个，是浅拷贝，直接复制。
这样声明
Clock(Clock &c)

4.关于对象指针
数据成员每个对象都有，函数成员是大家共享的。this只隐藏于每一个成员函数的特殊指针,this->x.

5.动态内存分配new和delete
动态创建堆对象。
Clock *c = new Clock();

6.深拷贝和浅拷贝
浅拷贝：如果对象中有指针的话，指针也会被复制，会指到同一个位置。

------------------------------------------------------
PS:
1.C++标准库：STL要熟悉，和模板是有区别的
2.C++保留了C语言的大部分库函数，另外加了模板和预定义类
3.两种include都可以，但只能选一种，如cmath math.h只能选择一种，风格要统一。