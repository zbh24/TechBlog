#gcc
gcc -O1 -o p p1.c p2.c

```
gcc -S:汇编代码
gcc -c:目标代码
gcc -o:可执行文件

objdump -d code.o:把目标代码变成汇编代码

gdb
x/13xb:
第一个x表示检查：
13个
第二个x表示16进制
b:一个字节

x/13xw

x/13db

x/s

p/s


(gdb) x/4xb &s
0xffffd028:	0xe5	0xbc	0xa0	0x00

ulimit -c 
```
经过我测试发现，在UTF-8编码下，大部分汉字是3个字节，ascii码是1个字节。

单核：通过调度多道程序
多核：多个cpu，真正并行化
超线程：一个cpu上即一个核上，可以有多个pc，即可以同时执行多个线程，即所谓的双核四线程。

```
git init
git remote add origin https://zbh24@bitbucket.org/zbh24/tinyfs.git

git add .
git commit
git push
```
gcc -m32:编译32位的代码
char,short,int都是以4字节对齐的

####setjmp
setjmp不会滚栈，无论是从man中得到信息，还是从汇编代码中得到的信息，我们都可以看出栈是不回滾的。

面试时除了刷题的以外，有两本面试必备：
csapp
apue
还有，鸟哥的那本也不错
