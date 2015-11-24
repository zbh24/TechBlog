#关于SSH以及网络
晚上，我在进行ssh相关的研究，然后发现一些其它问题。

####网络，路由
我的cmcc-edu的路由地址是218.205.9.243，这个路由都带着NAT转换功能。
nat就是：在路由器里面有着一张表
srcip port ---bcast__ip port1
也就是发出去的包，修改源ip和源端口，收到的包修改目的ip和目的端口。
```
traceroute baidu.com
对每个htop点，发3个包
这个功能的实现就是靠ttl
ping -t 1 baidu,com
```
我们想要上cmcc-edu，那么经常连不上，是由于分配DHCP动态分配ip地址不成功，所以我们可以手动写一个静态ip地址。

####ssh
ssh就是一种安全的远程登录。和telnet的区别，这个是远程连接，而且是明文的。而ssh是加密的。注意SSH是一种网络加密协议，而实际上ssh实现出好几种，开源的有openssh，这个是采用那个rsa加密的。注意，我们命令行下使用的ssh就是openssh。

####ssh登录方法
SSH分客户端openssh-client和openssh-server
如果你只是想登陆别的机器的SSH只需要安装openssh-client（sudo 
apt-get install openssh-client），如果要使本机开放SSH服务就需要安装openssh-server
然后确认sshserver是否启动了：
ps -e |grep ssh
如果看到sshd那说明ssh-server已经启动了。
如果没有则可以这样启动：sudo /etc/init.d/ssh start 或者 service ssh start
ssh-server配置文件位于/etc/ssh/sshd_config，在这里可以定义SSH的服务端口，默认端口是22，你可以自己定义成其他端口号，如222。
然后重启SSH服务：
sudo 
/etc/init.d/ssh stop
sudo /etc/init.d/ssh start
也可以这样更改端口
ssh -p 2222 user@host
然后使用以下方式登陆SSH：
ssh username@192.168.1.112 username为192.168.1.112 机器上的用户，需要输入密码。

####中间人攻击
SSH之所以能够保证安全，原因在于它采用了公钥加密。
整个过程是这样的：（1）远程主机收到用户的登录请求，把自己的公钥发给用户。（2）用户使用这个公钥，将登录密码加密后，发送回来。（3）远程主机用自己的私钥，解密登录密码，如果密码正确，就同意用户登录。
这个过程本身是安全的，但是实施的时候存在一个风险：如果有人截获了登录请求，然后冒充远程主机，将伪造的公钥发给用户，那么用户很难辨别真伪。因为不像https协议，SSH协议的公钥是没有证书中心（CA）公证的，也就是说，都是自己签发的。
可以设想，如果攻击者插在用户与远程主机之间（比如在公共的wifi区域），用伪造的公钥，获取用户的登录密码。再用这个密码登录远程主机，那么SSH的安全机制就荡然无存了。这种风险就是著名的"中间人攻击"（Man-in-the-middle attack）。
SSH协议是如何应对的呢？

第一次把公钥发送过来以后，以后就保存在本地了，不会再去读这个公钥了。
