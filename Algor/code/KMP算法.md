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
参考july算法：
http://wiki.jikexueyuan.com/project/kmp-algorithm/define.html