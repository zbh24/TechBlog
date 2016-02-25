# JAVA的实现

标签（空格分隔）： 未分类

---

我们知道C语言编译以后生成一个可执行文件（ELF）,有代码段，数据段，以及运行时会创建栈，堆。这样一个C语言程序就可以运行起来了。

但是，JAVA却不太一样，java的源程序.java编译以后生成.class字节码，然后JVM虚拟机解释执行.class字节码。
JVM有自己的指令结构，有自己的寄存器，有自己的处理器，有自己定义的数据段，代码段，有自己的堆。
这种编译实现方式跟C4有点像。

##CLASS的结构
CLASS文件结构跟C语言有点类似4。，主要有两类数据项，无符号数和表。
下面实际例子来说明
```
package com.ejushang.TestClass;
 
public class TestClass implements Super{
 
private static final int staticVar = 0;
 
private int instanceVar=0;
 
public int instanceMethod(int param){
 return param+1;
 }
 
}
 
interface Super{ }
```
所有的文字都放在常量池里面
第一个方法<init>:()V
fields_counts和fields_info

methods_count和method_info,
这都是结构体，有很多选项，然后里面有MAX_STACK，根据这个，虚拟机分配栈的大小

其中attribute_name_index指向常量池中值为Code的常量，attribute_length的长度表示Code属性表的长度（这里 需要注意的时候长度不包括attribute_name_index和attribute_length的6个字节的长度）。

max_stack表示最大栈深度，虚拟机在运行时根据这个值来分配栈帧中操作数的深度，而max_locals代表了局部变量表的存储空间。

max_locals的单位为slot，slot是虚拟机为局部变量分配内存的最小单元，在运行时，对于不超过32位类型的数据类型，比如 byte,char,int等占用1个slot，而double和Long这种64位的数据类型则需要分配2个slot，另外max_locals的值并 不是所有局部变量所需要的内存数量之和，因为slot是可以重用的，当局部变量超过了它的作用域以后，局部变量所占用的slot就会被重用。

code_length代表了字节码指令的数量，而code表示的时候字节码指令，从上图可以知道code的类型为u1,一个u1类型的取值为0x00-0xFF,对应的十进制为0-255，目前虚拟机规范已经定义了200多条指令。

exception_table_length以及exception_table分别代表方法对应的异常信息。

attributes_count和attribute_info分别表示了Code属性中的属性数量和属性表，从这里可以看出Class的文件结构中，属性表是很灵活的，它可以存在于Class文件，方法表，字段表以及Code属性中。

接下来我们继续以上面的例子来分析一下，从上面init方法的Code属性的截图中可以看出，属性表的长度为0x00000026,max_stack的 值为0x0002,max_locals的取值为0x0001,code_length的长度为0x0000000A，那么00000149h- 00000152h为字节码，接下来exception_table_length的长度为0x0000，而attribute_count的值为 0x0001，00000157h-00000158h的值为0x000E,它表示常量池中属性的名称，查看常量池得知第14个常量的值为 LineNumberTable，LineNumberTable用于描述java源代码的行号和字节码行号的对应关系，它不是运行时必需的属性，如果通 过-g:none的编译器参数来取消生成这项信息的话，最大的影响就是异常发生的时候，堆栈中不能显示出出错的行号，调试的时候也不能按照源代码来设置断 点，

##JVM概况
 Java virtual machine (JVM) is an abstract computing machine that enables a computer to run a Java program. There are three notions of the JVM: specification, implementation, and instance. The specification is a document that formally describes what is required of a JVM implementation. Having a single specification ensures all implementations are interoperable. A JVM implementation is a computer program that meets the requirements of the JVM specification. An instance of a JVM is an implementation running in a process that executes a computer program compiled into Java bytecode.
 
 ORALCE的JVM的实现是HOTSPOT，特征是JIT和适度优化。
 
###CLASSloader
 
1.Loading: finds and imports the binary data for a type
2.
- Linking: performs verification, preparation, and (optionally) resolution
Verification: ensures the correctness of the imported type
Preparation: allocates memory for class variables and initializing the memory to default values
Resolution: transforms symbolic references from the type into direct references.

3.Initialization: invokes Java code that initializes class variables to their proper starting values.

###JAVA bytecode
The JVM has instructions for the following groups of tasks:

Load and store Arithmetic Type conversion Object creation and manipulation Operand stack management (push / pop) Control transfer (branching) Method invocation and return Throwing exceptions Monitor-based concurrency

###JVM languages
There are several JVM languages, both old languages ported to JVM and completely new languages. JRuby and Jython are perhaps the most well-known ports of existing languages, i.e. Ruby and Python respectively. Of the new languages that have been created from scratch to compile to Java bytecode, Clojure, Groovy and Scala may be the most popular ones. A notable feature with the JVM languages is that they are compatible with each other, so that, for example, Scala libraries can be used with Java programs and vice versa.[6]

###Bytecode interpreter and just-in-time compiler
For each hardware architecture a different Java bytecode interpreter is needed. When a computer has a Java bytecode interpreter, it can run any Java bytecode program, and the same program can be run on any computer that has such an interpreter.

When Java bytecode is executed by an interpreter, the execution will always be slower than the execution of the same program compiled into native machine language. This problem is mitigated by just-in-time (JIT) compilers for executing Java bytecode. A JIT compiler may translate Java bytecode into native machine language while executing the program. The translated parts of the program can then be executed much more quickly than they could be interpreted. This technique gets applied to those parts of a program frequently executed. This way a JIT compiler can significantly speed up the overall execution time.

There is no necessary connection between Java and Java bytecode. A program written in Java can be compiled directly into the machine language of a real computer and programs written in other languages than Java can be compiled into Java bytecode.

Java bytecode is intended to be platform-independent and secure.[12] Some JVM implementations do not include an interpreter, but consist only of a just-in-time compiler.[13]

###oracle jvm
The JVM specification gives a lot of leeway to implementors regarding the implementation details. Since Java 1.3, JRE from Oracle contains a JVM called HotSpot. It has been designed to be a high-performance JVM.
To speed-up code execution, HotSpot relies on just-in-time compilation. To speed-up object allocation and garbage collection, HotSpot uses generational heap.

####Generational heap
The Java virtual machine heap is the area of memory used by the JVM for dynamic memory allocation.[22]
In HotSpot the heap is divided into generations:
The young generation stores short-lived objects that are created and immediately garbage collected.
Objects that persist longer are moved to the old generation (also called the tenured generation). This memory is subdivided into (two) Survivors spaces where the objects that survived the first and next garbage collections are stored.
The permanent generation (or permgen) was used for class definitions and associated metadata prior to Java 8. Permanent generation was not part of the heap.[23][24] The permanent generation was removed from Java 8.[25]
Originally there was no permanent generation, and objects and classes were stored together in the same area. But as class unloading occurs much more rarely than objects are collected, moving class structures to a specific area allowed significant performance improvements.[23]

