#关于科大VPN
[1]起因
我当时连不上vpn，我就直接登上了VPN.USTC.EDU.CN
然后就看到一条消息说vpn相关的已经转移到了
http://netfee.ustc.edu.cn/faq/index.html#howtosetupvpn

[2]继续
然后介绍了vpn分为两种。
网络信息中心提供两种类型的VPN：PPTP VPN和OpenVPN
前者Windows操作系统直接支持，不需要安装第三方软件
后者需要安装第三方软件，不容易受网络情况的影响，比较容易连接

[3]然后呢，PPTP VPN的设置
网络信息中心有两个PPTP VPN服务器：vpn1.ustc.edu.cn和vpn2.ustc.edu.cn。
其中，vpn1.ustc.edu.cn是电信IP，vpn2.ustc.edu.cn是教育网IP，用户在设置服务器时，可以根据自己所在网络选择合适的服务器。

常见错误：
VPN客户端拨入时出现619错误 
这种情况大数是无法与VPN服务器建立连接，可能是所在的运营商不支持VPN，或者客户机连接Internet的网关（如家庭宽带路由路）对VPN支持不好。

VPN客户端拨入时出现691错误 
这种情况大数多是用户名密码错误或者没有VPN权限，请登录 http:/wlt.ustc.edu.cn验证用户名密码是否正确、是否有VPN权限 。

[4]我就去检查权限，意外发现
然后，我登陆网络通，发现自己首先是拥有vpn权限的。
接着发现，可以设置出口。
我目前使用的是出口8，可以上google，但是上不了facebook。