#关于linux的常用方法二之shellscript
###vim
####vim搜索
？word ：向上查找单词
/word：向下查找单词
下一个：n
上一个：N

####vim操作
删除：向前一个字符x，向后一个字符X
删除当前行：dd
复制当前行：yy    复制光标向下的n行：20yy
粘贴到下一行：p
粘贴到当前行：P

####光标移动
移动到这行开头：0
移动到文件的开头：G
移动到文件的最后一行：1G

####其他操作
撤销上一个操作：u
重做上一个操作：ctr+r

####关于vim本身
1.～/.vimrc  ~/.viminfo
进行环境的设置
：set nu:这是设置显示行号 
：set nonu不显示行号
：set all：查阅有那些设置

2.vim的配置文件在/etc/vimrc下面，不过不建议直接修改vim
你可以修改在自己用户目录下的东西
~/.vimrc
set nu(或者：set nu)
set backtrace=2
syntax on
set showmode

###Bash
####shell
shell:就是先fork一个进程出来，然后exec一个程序。
1.bash有记忆功能，记忆在.bash_history里面。记录的都是前一次登录时使用的命令，这一次的都还在内存里面。注销系统以后，才会写进去。

PS:经过研究发现，每个shell进程都会有内存来保存这些命令。shell退出后，会把命令添加到末尾。先退出先添加到末尾。
shell进程启动以后。应该有两个数组，一个旧历史命令，一个新历史命令，查找历史记录时，如果这个新的没有了，则寻找旧的。
数据结构就是两个数组。

2.命令别名：
alias lm="ls -al"，看起来不错，不知道有什么用。

3.有时候一行命令不够不能输完，我们想换行继续输，可以这样作。
用\,然后回车，其实就是把回车转义。

####shell变量
1.变量被显示的时候，必须加$,如echo $PATH,echo ${PATH}。

2.设置变量。如name=zbh
1)
name="Bihong Zhang"
echo $name
name=Bihong\ Zhang:这样也对

2)
own="This is by $name"			
echo $own

3)增加内容
PATH=/home/zbh/sml:$PATH
如何其它程序也需要这个变量，可导出到环境，成为环境变量如，export zbh
PS：通常系统默认变量为大写，自己定义的可以小写。
最后取消变量名unset zbh

4)追加内容
name=“zbh”

name=$zbh24				wrong

name="$zbh"24

name=${zbh}24	这种写法最好

5)
cd /lib/modules/$(uname -r)/kernel
cd /lib/modules/`uname -r`/kernel:反单引号内容先执行
PS:里面是命令则是$（），否则变量则是${}

6）
myname="$name is me"

myname='$name is me'

这两个是有区别的，“识别变量”，'不识别变量'

####环境变量的功能
[1]
env：环境变量，set另外包括自定义变量
[2]
set:可以看到PS1,这个变量，这个变量很好玩，是设置shell页面一部分的，我们可以去设置改变。
[3]
$$:$本身也是一个变量，代表线程号PID,可以echo $$
[4]
?:这也是一个变量，上一个命令的回传值，上一个命令成功的执行，则为0，否则为非0.   echo $SHELL echo $?

PS:新机器可以装老软件，但是老机器装不了新软件，这个64位系统最能说明道理。

环境变量和自定义变量的区别就是，能不能影响到子进程中去，要想影响到，export，所以，把自定义变量变成环境变量，就要export。

[5]
histpry -w:立即把内存中的命令写入到bash_history
开一个终端，就会有自己的内存记录，history -w只是把自己这个终端记录写进去，其它的要等到注销系统后才会写进去，

[6]设置别名
alias ls='ls --color=auto'
unalias ls:就可以取消设置了

这样可以分析grep：
type -a grep
grep is aliased to `grep --color=auto'
grep is /bin/grep

####bash的操作环境

1）欢迎界面，这个纯属好玩。
/etc/issue

2)配置文件
整个系统的/etc/profile ：
在这个里面会有path，histsize阿等等

个人 的~/.bash_profile:如果要修改数据，就修改这里。
在我的ubunt里面，这里是.profile.没有其它文件。
这里也有path的设置，我们have a try。
证明是可以的。
这个文件会调用.bashrc的。
**最终被读取的配置文件是.bashrc，所以也可以把偏好也在那儿**
**看看我们bashrc设置的这些，明白了吧**
75      alias ls='ls --color=auto'
 76     #alias dir='dir --color=auto'
 77     #alias vdir='vdir --color=auto'
 78 
 79     alias grep='grep --color=auto'
 80     alias fgrep='fgrep --color=auto'
 81     alias egrep='egrep --color=auto'

3)读取文件配置命令source
因为普通的得注销以后，读取才能生效，我们直接生效。
这样也可以 .，跟source功能一样。

3）通配符
*:0个或者任意多个占位符
?:一个任意占位符
[Tt]:和[T|t]等价
[0-9]：0-9任意数字
[^TtAa]:不能以这些开头的

例子：[^a-z]*

###数据流重定向
####标准输出
>:替换
>>:累加
如 ll / > myfile
ll  /etc/ > myfile
ll /home/zbh >> myfile
PS:标准输出是1 >和1>>，标准错误呢是 2>和2>>


 find / -name .bashrc  > right.txt
 这样会把正确的输出到right里面，像那些permission denied就会忽略掉。
 
 find / -name .bashrc  > right.txt 2> wrong.txt
 这样正确错误的都会有了，但是屏幕上什么也不会有
 
####设备黑洞
去掉错误信息
find / -name .bashrc  2> /dev/null
find / -name .bashrc  2> wrong.txt
 
 如果把正确和错误输入到同一个文件呢
 这样写find / -name .bashrc  > right.txt 2> right.txt
 是错误的。
 
 正确写法：
 find / -name .bashrc > right.txt 2> &1
 
 
####标准输入
cat > list.txt < ~/.bash_history：有bash_history来填充

cat > list.txt << "eof"：遇到eof表示输入结束，自动结束。

####命令执行的判断依据(; && || )
;使用于前后两个命令毫无相关性

###相关性的&&和||
感觉这里有点惰性就算的意思，我们知道前一个成功执行，所以&&就会执行下一个，||下一个就不会执行。
PS：&&这么理解，第一个执行正确，肯定会去判断第二个。如第一个执行错误，那就没有必要里。

ls /mnt/flash && echo "exist" || echo "not exists"
不能根据echo $?是否返回0来理解，那样刚好理解反了。

####管道命令
**管道|:第一个必须为stdout，第二个必须为命令，且可以接受stdin,这样的才能使用管道**

[1]
cut命令：对每行进行处理
echo $PATH | cut -d ":" -f 1-3
 last | cut -d " " -f 1 > ~/test
 export | cut -d " " -f 3
 这个功能感觉确实还比较好用。
export | cut -d " " -f 1-1,2-3

[2]
grep:选出符合规定的某一行
grep -rn "zhangbihong" ./
-v:反向选择
-i：忽略大小写
-A B: grep -rn "spin" -A 20 -B 1 ./
grep -rn "^自旋" ./
grep -rn "[^自旋]自旋" ./

[3]排序sort wc uniq
sort：sort -t ":" -k 3:
以：分隔，然后第3个领域来排序

uniq：不显示 重复的数据

wc -lwc

[4]tee双重定向
既输出到屏幕，还输出到file
ls -l > tee hello.txt
屏幕和文件都有

[5]字符转换命令
head -n 3
tail -n 10
more: set | more -d
less
dmesg
tcpdump

[6]xargs
这个命令就是产生某个命令参数的意思，因为有的命令不支持管道，就需要xargs来帮忙了。
find / -name "zhang" | xargs ls -l

[7]tar
tar -cvf dftl.tar deftl /:压缩
tar -xvf dftl.tar:解压缩
