#操作系统以及csapp的信号
####系统调用和终端，trap
虚拟地址和物理地址。
虚拟地址是由（段地址和页地址，组合起来的）
内核都在高地址指的就是虚拟地址。

- 所谓的内核和用户态切换就是这个意思，会有段地址的切换。运行在内核态时可以执行任何指令，因为页面地址的标志位上有这个标志。
- 每个进程仿佛自己都拥有4G的地址空间
- 上下文切换（context switch）是用来进行多任务的

####进程
- fork就会产生一个新进程，新进程有新的地址空间和程序计数器。两个进程不好说，哪一个先执行结束，不知道，那shell里面是怎么做的，为何父进程是在等待子线程结束呢。如果在命令后面加一个&,那么不会等待shell不会等待它完成，这个进程会在后台执行，知道结束。
因为shell进程调用了一个函数waitpid函数来等待子进程结束。
fork execve
- pthread是会产生一个新的线程。
- 比较fork和pthread，也就是进程和线程的区别。进程有独立的地址空间，但是线程就没有。比较对于 i = i +1，这种多个线程操作就会产生错误，是线程不安全的。

####shell
有时候，我们发现，有些命令比如ls，ping可以在/bin下可以找到相应的程序，但是有的就找不到，找不到的是shell的内置命令。
shell会判断是内置命令(如fg bg)，还是可执行程序(ping ls)之类的，要是后者就执行execve，进行加载。

####信号
信号是一种高级的软件形式的异常。
其实，信号就是属于进程间的一条消息，用来通知作用的。

- 比如，你这个进程内存溢出了，先发生中断，陷入到内核里面，然后异常处理程序给你，也就是这个进程发一个信号，告诉你这个进程，内存溢出了。
- 再比如处以0，内核会给你发信号，浮点异常。
- 再比如你在键盘上按ctr + c，内核就会给你这个进程发一个终止，sigint，键盘中断。ctr + z：挂起进程。
- 有内核的异常处理程序发送信号，那么就有进程的接受信号，接受的行为是handler
- strace ps top pmap /proc/cpuinfo

```
zbh@zbh-TM4750:~$ kill -l 
 1) SIGHUP	 2) SIGINT	 3) SIGQUIT	 4) SIGILL	 5) SIGTRAP
 6) SIGABRT	 7) SIGBUS	 8) SIGFPE	 9) SIGKILL	10) SIGUSR1
11) SIGSEGV	12) SIGUSR2	13) SIGPIPE	14) SIGALRM	15) SIGTERM
16) SIGSTKFLT	17) SIGCHLD	18) SIGCONT	19) SIGSTOP	20) SIGTSTP
21) SIGTTIN	22) SIGTTOU	23) SIGURG	24) SIGXCPU	25) SIGXFSZ
26) SIGVTALRM	27) SIGPROF	28) SIGWINCH	29) SIGIO	30) SIGPWR
31) SIGSYS	34) SIGRTMIN	35) SIGRTMIN+1	36) SIGRTMIN+2	37) SIGRTMIN+3
38) SIGRTMIN+4	39) SIGRTMIN+5	40) SIGRTMIN+6	41) SIGRTMIN+7	42) SIGRTMIN+8
43) SIGRTMIN+9	44) SIGRTMIN+10	45) SIGRTMIN+11	46) SIGRTMIN+12	47) SIGRTMIN+13
48) SIGRTMIN+14	49) SIGRTMIN+15	50) SIGRTMAX-14	51) SIGRTMAX-13	52) SIGRTMAX-12
53) SIGRTMAX-11	54) SIGRTMAX-10	55) SIGRTMAX-9	56) SIGRTMAX-8	57) SIGRTMAX-7
58) SIGRTMAX-6	59) SIGRTMAX-5	60) SIGRTMAX-4	61) SIGRTMAX-3	62) SIGRTMAX-2
63) SIGRTMAX-1	64) SIGRTMAX	
```
- shell使用job这个概念来描述shell创建的新进程。

**终于，大概明白了信号是怎么回事了。**

####并发和线程

####
1.6.828 xv6
2.scheme解释器

