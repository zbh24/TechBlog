#正则表达式
正则表达式是一种表示法，只要工具支持，那么就可以使用正则表达式来处理字符串。如grep，sed，awk。
注意，正则表达式和通配符的区别。
cp和ls不支持正则表达式，只支持通配符。

通配符：如
- *表示，任意多个字符     **ls te***
- ？表示一个字符  **ls te？**
- [Tt]:T或者t **ls te[012]**
- [0-9]:0 到9都符合 **ls [1-2]**
- [^tT]：不能这些开头 **ls te[^1]**

总体感觉，部分类似，但是大部分不一样，*和？就不一样。
PS：通配符里面，[Tt]是正常的，[T|t]是非法的。

####扩展的正则表达式
一般基础的表达式只能这样 [T| t]
但是，扩展的可以这样，（fixpoint | inductive ）
grep -E ：表示扩展

####grep的一些参数
- A:after -A 10
- B:before -B 10
- i:ingore 忽略大小写
- n:行号，number
- --color=auto
- r： recurison，递归地查找，如果有目录
- v： 反转，不符合地显示

####基础正则表达式
[1] 例子
```
grep -vn "the" hello
grep -n "t[ae]st" hello
greo -n "[^g]oo" hello
grep -n "[^a-z]oo" hello
grep -n [0-9] hello
grep -n "^the" hello
grep -n "^[^a-zA-Z]" hello  //不要英文字母开头
grep -n "\.$" hello  //以.结尾那一行，.表示占位符，所以转义
grep -n "^$" hello //找出空白行
grep -n "g..d" hello //两个占位符
grep -n "ooo*" hello //o至少出现两个
grep -n "g.*g" hello //.是占位符的意思，这样就是任意个字符
grep -n "o\{2\}" hello //重复两次的意思
grep -n "o\{2，5\}" hello
grep -n "o\{2，\}" hello  
grep -n "o\{，5\}" hello  
```
具体一些规则：
- ^: 表示以这开头
- $:表示以这个结尾
- \\:转义
- [list]:任选字符
- [n1-n2]:从n1-n2，根据ascii值
- [^list]：不以这个开头
- *:前面字符重复0到无穷次
- \\{n,\\m}:这是重复次数

下面这是扩展
- ?:0或者1次
- +:1到无穷次
- (abc|ABC):abc或者ABC,这是组字符串

```
zbh@zbh-Latitude-E5440:~$ grep -E "(abc|ABC)" hello 
abc ABC
zbh@zbh-Latitude-E5440:~$ grep -E "[abc|ABC]" hello 
zhang Zhang
abc ABC
zbh@zbh-Latitude-E5440:~$ grep  "[abc|ABC]" hello 
zhang Zhang
abc ABC
zbh@zbh-Latitude-E5440:~$ grep  "[abcABC]" hello 
zhang Zhang
abc ABC


```
这说明，[abc|ABC]和[abcABC]没有区别，也不是扩展正则表达式。
PS:我的邮箱：
^[a-zA-Z0-9]\\{4,10\\}\@[a-zA-Z0-9]\\{1,10\\}\.com
####其它工具
sed：用来处理行
awk：用来处理每行的列

####diff，cmp，patch
[1]
diff：比较两个文件，以行为单位
- B:空行
- b：一行中的空格
- i:一行中大小写
number start ,hash,number start
diff -B left right:忽略空行

[2]
cmp是以字节为单位的

[3]
升级就是比较新旧文件的不同，如果把不同的制作成补丁，然后由补丁来升级旧文件。
patch命令就是diff来生成补丁的。


