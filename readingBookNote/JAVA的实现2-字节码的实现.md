# JAVA的实现2-字节码的实现

标签（空格分隔）： 未分类

---

1.java语言的规范和JVM的规范
2.Java的字节码：


- One-byte instructions
- 256 possible opcodes
- 200+ in use

3.分为这几部分
stack manicpulation
flow control
object model
arithmetics
monitorenter monitorexit

4.javap
Java class file disassembler
就像objdump一样，执行文件ELF很大，你可以根据选项，选出你想要的那部分。

• Used with no options shows class structure
only
– Methods, superclass, interfaces, etc
• -c shows the bytecode
• -private shows all methods and members
• -s prints internal signatures
• -l prints line numbers and local variable
tables

5.
public class Hello extends java.lang.Object{
public Hello();
Code:
0: aload_0
1: invokespecial #1; //Method java/lang/Object."<init>":()V
4: return
public static void main(java.lang.String[]);
Code:
0: getstatic #2; //Field java/lang/System.out:Ljava/io/PrintStream;
3: ldc #3; //String Hello, World!
5: invokevirtual #4; //Method java/io/PrintStream.println:(Ljava/lang/String;)V
 
 
###MODEL OFCOMPUTATION
####Stack Machine
JVM is a stack-based machine
Each thread has a stack
Stack stores frames
Frame is created on method invocation
Frame consists of:
– Operand stack
– Array of local variables


The Frame：

- local variables
- operand stack 
- #1,#2(指向常量池constant pool)
也就是一个局部变量表，然后一个操作数栈。
然后一个常量池。
运行那个代码时，load的#1就指向常量池。
在局部变量表和stack之间，互相转变，是通过。
laod和store的操作。

####STACK CRUNCHING
栈上的各种操作

####LOCAL VARIABLES
```
LocalVariableTable:
Start Length Slot Name Signature
0 5 0 this LLocalVariables;
0 5 1 value I
```
最重要：
也就是一个局部变量表，然后一个操作数栈。
然后一个常量池。
运行那个代码时，load的#1就指向常量池。
在局部变量表和stack之间，互相转变，是通过。
laod和store的操作。

###Objects
1）对象初始化：
new:初始化
<init>：Instance initialization method
<clinit>：Class and interface initialization method
```
static {a = 1;}
static {b = 1;}

static {};
Code:
0: iconst_1
1: putstatic #2; //Field a:I
4: iconst_2
5: putstatic #3; //Field b:I
8: return

```
其它类似

###METHOD INVOCATION

- invokestatic:  例如：Integer.valueOf("42")
- invokespecial: <init>,void foo(),super.method() 
- invokevirtual：this.add(1,2);
- invokeinterface：实现接口呗
- invokedynamic:动态绑定

1）第一个例子：
obj.method(param1, param2);
code:
push obj
push param1
push param2
call method

2)
```
this.add(1, 2);
0:aload_0
1:iconst_1
2:iconst_2
3:invokevirtual #2; //Method add:(II)I
```
-----------------------------------------------

Multiple bytecodes for method lookup
invokevirtual - when class of object known
invokeinterface - when interface of object known
invokestatic - static methods
invokespecial - some special cases

例子：
```
Java
JVM Activation Record
Class A extends Object {
int i;
void f(int val) { i = val + 1;}
}
```
```
Bytecode
Method void f(int)
aload 0 ; object ref this
iload 1 ; int val
iconst 1
iadd ; add val +1
putfield #4 <Field int i> // #4 refers to constant pool
return
```
JIT技术：
Method can be executed as interpreted 

Bytecode Compiled to machine code, initially or on nth execution Compiled native code stored in cache 

If cache fills, previously compiled method flushed