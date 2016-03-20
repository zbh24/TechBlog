# ADT之SML中的数据类型，以c语言的泛型

标签（空格分隔）： 未分类

---

1.sml中有sigature和structute，就相当于一个接口，一个是实现。但这是为了实现隐藏技术的，如果你没有在sigature中声明，那么你就不能使用。
这种技术会隐藏实现，但是有两种方式稍微有点区别。
1）透明的，这种不隐藏类型定义。:
2）不透明的，连定义类型都隐藏了，强迫您使用ADT。:>

2.以前在C语言中也使用ADT,就是你在头文件中声明，但是实现在.c文件里面。这样，你可以只给个头文件，然后一个库文件，然后就实现了细节的隐藏。

3，拿C语言来说明一个例子阿：
1）头文件定义一个栈，及操作。
```
stack.h
struct stack {
    int *base;
    int size;
} stack

int enstack(struct stack)
```
这样的话还是暴露了类型的定义。

2）可以这样定义头文件
```
typedef struct list *list;

list creat(int data,list next);

int length(list l);
```
这样就隐藏了list的定义了。
这就是ADT。

同样的C语言也可以定义泛型了。
以下分为了C++,JAVA的泛型。
```
//模板，泛型
//STL就是标准模板库
//STL模板的使用#include<vector> #include<algorithm>
//c++的模板是用泛型写的，这样什么类型都能使用

template <typename X>	//或者这样声明template <class X>
X f(X a) {		//X ->X
	return a;
}

int main() {

	int x = f<int> (100);
	double y = f<double> (3.14);
	cout<<x<<y<<endl;
	return 0;

}
//////////////////////////////
template <class T>
class Array{
	
public:
	Array(int);
}

template <class T>
Array<T>::Array(int a) {
	
}

int main() {

	Array<int> a(100);
}
```
JAVA的泛型是这样定义的：
```
class A<T1,T2> {
	T1 first;
	T2 Second;
	A(T1 first,T2 second) {
		this.first = first;
		this.second = second;
	}
	
	public static void main(String []args) {
		A<int,char> a = new A<int,char>; 
	}

```
那么C语言的泛型是怎么定义呢？
```
#define List(X) \
struct list_##X{  \
	X data;	\
	struct list_##X *next;	\
} ;\
\
int list_##X##_length(struct list_##X l) { \
	return 0;	\
}	\
\
struct list_##X 

int main () {
	List(int) l;
	List(double) l1;
}
```
利用宏定义这个技巧去实现的，停有意思的。
