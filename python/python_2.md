#python2

####路径和包
[1]
路径的概念
```
import sys
sys.path.append("/home/zbh/test")
#就会到那下面找我的模块

#加入这个模块是这样写的hellozbh.py
def hello():
	print "hello,world"
#这样使用
import hello
hellozbh.hello()
```
[2]
一个模块中的有很多函数，一个包里有很多模块。
在目录里加一个___init____.py
引用这么作
```
import dir
import dir.fst_module
from snd_module import dir
```

####模块
```
import copy
dir(copy)
help(copy._test)

help(copy.__doc__)
help(copy.__file__)
```

###标准库
**sys os fileinput time**

[1]
SYS模块
sys的path，argv

[2]
OS模块：主要是为了系统功能
每个模块中都有参数和函数
java包，我们只会用到函数
```
os.system("~/chrome")
```
[3]
数据结构
集合：set([2,3,4,2]) ---> ser ([2,3,4])

[4]
堆函数
```
from heapq import *
```
range(10)这是程序自带的属性

[5]
time
```
help(localtime)

localtime([secns]) ---> sum yaer

localtime(34334354) right
localtime([345t3453]) wrong
```
