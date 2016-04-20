#关于linux的常用方法一
###inode与block
[1]
superblock：一个超级块儿，记录整个文件系统的inode和block的使用量
inode：记录文件的权限和属性，一个文件占用一个inode，同时记录这个文件所在的block号码，可以有多个block号码
block：实际文件数据，一个文件可以占用多个block
PS：这是linux的ext2文件系统使用的方法，并不是所有的都这么作，如闪存的FAT就不是。
FAT系统就没有inode，后一个bock都记录在前一个block里面。

###挂载点
[1]
文件系统必须挂载在目录树上才能进入，挂载点就是目录树。文件系统都是通过挂载点进入的。
由于硬件都是文件，所以在linux里面都是把硬件（其实就是文件）挂载到目录树上。
如mount /home/zbh /dev/hdc2
这就是目录树和磁盘中的数据关系。
所谓挂载就是利用一个目录当成进入点，将磁盘分区的数据放置在该目录下，也就是说，进入该目录就可以读取该分区的数据，这个操作称为挂载，进入的目录成为挂载点。

磁盘分区是硬件问题。
目录树是软件问题。
这两个是独立的。
可以把光驱的数据挂载到/mnt/我的文件

装linux可以之用两个分区 /和swap，其实是两个挂载点。

文件系统																		挂载点
/dev/hdc2（相当于D盘，ext2文件系统）					/home
/dev/hdc3（相当于E盘，ext3文件系统）					/home/zbh

**这种文件系统的概念和ext2的概念是不一样的**

[2]
目录的数据块记录文件名和对应的文件的inode。
文件名一定是记录在目录的数据块中。新增，删除，以及重命名与目录的w权限有关。
ls -li
可以查看inode几点信息。
ext3增加了日志功能，让数据保持一致性，防止崩溃，快速恢复。
目录数据块是这样的结构
inode			文件名

###root和权限
1.ubuntu一开始是有root用户的，但密码没有开启，需要手动设置密码。

2.更改密码
passed zbh
passwd root

3.
如果这个文件，有人拥有执行权限，root一定拥有。如果都没有，那么root也没有，因为它不认为这是个命令。

4.
多用sudo，少用root权限。

5.
sudo 创建的文件也是root，root的，一般创建的文件默认是644

6.
chmod有没有改动的权限跟RWX,没有任何关系，跟这些没有关系。

7.对于rw，不管这个文件的权限如何，root都有读写权限。可能写得时候要加wq!,强制写入。
对于执行，比如可执行脚本，还是先修改成可执行文件，再进行执行。

###ln
**软链接和硬链接，软链接就相当于快捷方式**

**硬链接：hard link**
就是修改目录的数据块，增加一个链接到原文件的inode节点。
ln src des
ll -i：可以发现inode是 一样的
删除后一个文件，就是在目录里面把文件名删除去。

**软链接：symoblic link**
就是快捷方式，它是新建一个文件（inode和block），然后指向被链接的文件的目录的文件名。所以一旦源删除，就无法访问。
ln -s src dst
ln -s ~/home/zbh/code/cat.c  /tmp/newfile.c

###其它
[1]
man
man 3 system
man man
PS:
1代码在shell环境中：（**可执行的程序或者shell 命令**）
2代表系统内核可调用的函数：（**内核提供的系统调用**）
3.常用的函数库，大部分为C的库函数：（**函数库调用，上面的是系统调用，库函数一般由系统调用组成**）

[2]
ls [option] [file]
这[]表示可选命令

[3]下载
wget url -O outputname
wget www.baidu.com -O zbh.index

####普通操作

cp rm mv
-r:recur
-f:force
####查找文件

**which** 查找执行文件（binary）在哪儿啊 which man

**一般查找文件whereis locate find**

whereis:查找文件在哪儿 whereis man
但是，find比较慢，而whereis和locate比较快，因为他们是在数据库里面查找，而不是在硬盘上。

**locate的使用**

locate 比较强大，后面设置能接正则表达式来查找文件。
locate ping:会找到很多
locate -r ping：这是正则表达式

**find的用法**

find [path] [option] [action]
这是在硬盘上找东西
find /home -user zbh:查找home下的属于用户zbh的东西。
find /etc -name “zbh”
find /home -name “ping*”
find / -type s

**tar**
打包： tar -cvf dst src
解包：tar -xvf filename

####查找内容
**grep**
> 典型用法：
grep -rn skip  ./ 
grep -rn "[T|t]o Bihong" ./ 或者这样表示 grep -rn "T*t*o Bihong" ./
*
?

 Repetition
       A regular expression may be followed by one of several repetition operators:
       ?      The preceding item is optional and matched at most once.
       *      The preceding item will be matched zero or more times.
       +      The preceding item will be matched one or more times.
       {n}    The preceding item is matched exactly n times.
       {n,}   The preceding item is matched n or more times.
       {,m}   The preceding item is matched at most m times.  This is a GNU extension.
       {n,m}  The preceding item is matched at least n times, but not more than m times.

PS:这里的*号和其它那里的*号有点不一样。
在别的地方，*号和？号是占位符的意思，尤其是在文件名表示的时候。
*表示任意多个字符的通配符。？表示一个字符的通配符。
如：
find ./ -name "cstdbool" right
find ./ -name "*bool"  right
find ./ -name "?stdbool" right
find ./ -name "bool" wrong

但是，在文件里，处理字符，即内容时
grep “bool” right

####磁盘分区
fidsk -l ： 查看所有分区
PS:必须root权限
