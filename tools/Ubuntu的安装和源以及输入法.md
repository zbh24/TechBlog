# Ubuntu的安装和源以及输入法

标签（空格分隔）： 未分类

---

1.因为Ubuntu软件包的安装方式是通过deb的方式进行安装的。也可以通过apt get install的方式进行安装。所以，接下来就要有源的列表。
/etc/apt/sources.ist
我的源是这样的。
```

deb http://mirrors.aliyun.com/ubuntu/ trusty main universe restricted multiverse
# deb-src http://mirrors.aliyun.com/ubuntu/ trusty main universe restricted multiverse
deb http://mirrors.aliyun.com/ubuntu/ trusty-security universe main multiverse restricted
# deb-src http://mirrors.aliyun.com/ubuntu/ trusty-security universe main multiverse restricted
deb http://mirrors.aliyun.com/ubuntu/ trusty-updates universe main multiverse restricted
#deb-src http://mirrors.aliyun.com/ubuntu/ trusty-updates universe main multiverse restricted 
deb http://mirrors.aliyun.com/ubuntu/ trusty-proposed universe main multiverse restricted
# deb-src http://mirrors.aliyun.com/ubuntu/ trusty-proposed universe main multiverse restricted
 deb http://mirrors.aliyun.com/ubuntu/ trusty-backports universe main multiverse restricted
# deb-src http://mirrors.aliyun.com/ubuntu/ trusty-backports universe main multiverse restricted


deb http://mirrors.163.com/ubuntu/ trusty main universe restricted multiverse
# deb-src http://mirrors.163.com/ubuntu/ trusty main universe restricted multiverse
deb http://mirrors.163.com/ubuntu/ trusty-security universe main multiverse restricted
# deb-src http://mirrors.163.com/ubuntu/ trusty-security universe main multiverse restricted
deb http://mirrors.163.com/ubuntu/ trusty-updates universe main multiverse restricted
#deb-src http://mirrors.163.com/ubuntu/ trusty-updates universe main multiverse restricted 
deb http://mirrors.163.com/ubuntu/ trusty-proposed universe main multiverse restricted
# deb-src http://mirrors.163.com/ubuntu/ trusty-proposed universe main multiverse restricted
 deb http://mirrors.163.com/ubuntu/ trusty-backports universe main multiverse restricted
# deb-src http://mirrors.163.com/ubuntu/ trusty-backports universe main multiverse restricted
```
每一行的开头是deb或者deb-src，分别表示直接通过.deb文件进行安装和通过源文件的方式进行安装。

deb或者deb-src字段之后，是一段URL，之后是五个用空格隔开的字符串，分别对应相应的目录结构。在浏览器中输入http://archive.ubuntu.com/ubuntu/，并进入dists目录，可以发现有5个目录和前述sources.list文件中的第三列字段相对应。任选其中一个目录进入，可以看到和sources.list后四列相对应的目录结构。

有的时候，在老版本上安装软件的时候会出现404 NOT FOUND,是因为每个版本的维护时间有长短问题，所以这个时候，就要打开list，进行版本号的替换，换成最新版本号的。然后呢,sudo apt-get update，来更新一下源。

2.也可以用直接下载deb包的方式来安装软件
1）下载一个deb格式的软件kismet
curl https://www.kismetwireless.net/code/dists/quantal/kismet/binary-i386/kismet-2011.03.2.i386.deb >kismet-2011.03.2.i386.deb

2）安装kismet
dpkg -i kismet-2011.03.2.i386.deb

（根据Ubuntu中文论坛上介绍，使用apt-get方法安装的软件，所有下载的deb包都缓存到了/var/cache/apt/archives目录下了，所以可以把常用的deb包备份出来，甚至做成ISO工具包、刻盘，以后安装Ubuntu时就可以在没有网络环境的情况下进行了）


----------------------------------------------------------------------
1.ubuntu下面输入法有两个输入法框架一个自带的IBUS，还有一个是fcitx框架。在这两个框架中，都可以安装很多输入法，所以这就是ubuntu安装输入法的方法。
我这个设置的快捷键是这样的。
1.对于我设置的这样的。ctr=A或者L-shift触发输入法框架，相当于激活呢。
2.然后ctr+shift进行输入法切换。

----------------------------------------------------
1.桌面崩溃以后，这样进行重新安装桌面
1）sudo apt-get update:更新源
2):sudao apt-get install --reinstall ubuntu-desktop
3)sudo apt-get install unity