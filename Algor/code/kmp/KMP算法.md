# KMP算法

标签（空格分隔）： 未分类

---

1.kmp算法最重要的就是生成next数组，那么怎么生成呢。
手动生成，就是求最长的前缀和后缀，然后后移动一位，最后左边补上-1.

2.代码生成next数组，可以这样一步步去做。
已知 next [0, ..., j]，如何求出 next [j + 1] 呢？
前提是next[j] = k （表示前0到k-1个字符等于j-k 到j-1个字符相等）
1）若p[k] == p[j]，则 next[j + 1 ] = next [j] + 1 = k + 1；

2）若p[k ] ≠ p[j]，如果此时 p[ next[k] ] == p[j ]，则 next[ j + 1 ] = next[k] + 1，否则继续递归前缀索引 k = next[k]，而后重复此过程。

解释一下为何递归前缀索引k= next[k]，就能找到长度更短的相同前缀后缀呢？

这又归根到 next 数组的含义。我们拿前缀 p0 pk-1 pk 去跟后缀 pj-k pj-1 pj 匹配，如果 pk 跟 pj 失配，下一步就是用 p[next[k]] 去跟 pj 继续匹配，如果 p[ next[k] ]跟 pj 还是不匹配，则需要寻找长度更短的相同前缀后缀，即下一步用 p[ next[ next[k] ] ] 去跟 pj 匹配。此过程相当于模式串的自我匹配，所以不断的递归 k = next[k]，直到要么找到长度更短的相同前缀后缀，要么没有长度更短的相同前缀后缀。如
这就是next数组的求出过程。

```
int gennext(string s) {
  int len = s.length();
  int k,j;

  j = 0;
  k = -1;
  next[0] = -1;
  
  while(j < len -1) {
    if(k == -1 || s[j] == s[k]) {
      k++;
      j++;
      next[j] = k;
    } else {
      k = next[k];
    }
  }
  return 0;
}
```

前缀和后缀：
ABCDAB：
前缀为：A，AB，ABC，ABCD，ABCDA
后缀为：BCDAB，CDAB，DAB，AB，B
所以最大长度为2,即是AB。


举个例子证明为什么不回退是正确的。
主串：ABAzzzzzzzzzzzzzzzz
模串：ABAxxxxxxxxxxxxxx

现在匹配到z和x不匹配了，我们主串没有回退，而是直接停留在那儿？为什么可以这样作呢。
因为我们要用到我们已经匹配到的信息，我们证明了前三个字母是相等的，假设反问一下，如果我们要是回到主串第二个BAzzzzzzzzzzzz
开始匹配并在z位置之前匹配成功，要求是什么，要求模串前两个是BA。但是，根据已经匹配到的信息，模串的后缀即后两个BA肯定是相等的，但根据NEXT数组，
没有这样前缀的存在，所以，回退是没有用的，多余的，所以不用回退那儿。


参考july算法：
http://wiki.jikexueyuan.com/project/kmp-algorithm/define.html
