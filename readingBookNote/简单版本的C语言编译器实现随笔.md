# 简单版本的C语言编译器实现随笔

标签（空格分隔）： 未分类

---
最近看了一个简单版本的C语言编译器的实现，感觉很有意思，很有感触，特地来写下来。
这个编译器其实是解释器，不过它是事先定义了一套虚拟机指令，然后编译生成这个虚拟机的指令，然后去解释执行(eval)这个虚拟机的指令，感觉这个方式跟java的编译有点像。

具体的整个实现是这样的。
1.定义出虚拟机的指令结构，和这个程序运行的结构，就像C语言一样，有代码段，数据段，有栈，有堆。
2.然后去实现这个虚拟机的所有指令，就是eval解释执行整个虚拟机。
3.然后真正开始编译整个C语言程序，首先词法分析，然后生成一个符号表。
4.然后语法分析，使用递归下降，也就是LL(1)文法。由于语法分析本身比较复杂，所以我们将它拆分成3个部分进行讲解，分别是：变量定义、函数定义、表达式和语句(statement和expression)。
5.然后生成中间代码，也就是我们定义的虚拟机指令,生成相应的文件，包括代码段，数据段，栈,堆。
6.没有进行代码优化，不过也可以去消除中间冗余代码。

真个整个编译架构大致如下：
next() 用于词法分析，获取下一个标记，它将自动忽略空白字符。
program() 语法分析的入口，分析整个 C 语言程序。
expression(level) 用于解析一个表达式。
eval() 虚拟机的入口，用于解释目标代码
不过，整个代码我还没有仔细阅读过，有时间仔细研读一下代码。

最后，教程的地址在：
http://lotabout.me/2015/write-a-C-interpreter-0/
其它有意思的参考资料：
Let's Build a Compiler
http://compilers.iecc.com/crenshaw/

PS:BNF等价于上下文无关文法。EBNF是扩展的BNF文法描述
如：
BNF：表达式 -> 表达式 + 项 | 表达式 - 项 | 项

EBNF：表达式 -> 项 {(+ | -)项}


