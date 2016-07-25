# stack算法和hash—array算法

标签（空格分隔）： 未分类

---

1.stack算法、
比如leetcode的84题就是这样，找出最大的长方形。我的思路是这样，利用一个栈，然后栈里面存的都是递增的数字。如果遇到当前的比栈顶大，就继续压栈。如果小，就退出来，然后进行计算。
```
int largestRectangleArea(vector<int> &height) {
        int n=height.size();
        if(n == 0) return 0;
        if(n == 1) return height[0];
        
        height.push_back(0);
        n++;
        
        int ans=0;
        stack<int> s;
        
        int i=0,j=0,h=0;
        while(i<n){
            if(s.empty() || height[i]>height[s.top()]) 
	      s.push(i++);
            else{
                h=height[s.top()];
                s.pop();
                j= s.empty() ? -1:s.top();
                ans=max(ans,h*(i-j-1));
            }
        }
        return ans;
 }
```
这里有个技巧，就是加了0到末尾来充当哨兵，这是个非常棒的想法。
http://www.geeksforgeeks.org/largest-rectangle-under-histogram/
这里有详细的解释，那么我现在提供个简单的解释。
How to calculate area with ‘x’ as smallest bar? We need to know index of the first smaller (smaller than ‘x’) bar on left of ‘x’ and index of first smaller bar on right of ‘x’. 
就是位置和高度。
下面是这个的详细算法
1) Create an empty stack.
2) Start from first bar, and do following for every bar ‘hist[i]’ where ‘i’ varies from 0 to n-1.
a) If stack is empty or hist[i] is higher than the bar at top of stack, then push ‘i’ to stack.
b) If this bar is smaller than the top of stack, then keep removing the top of stack while top of the stack is greater. Let the removed bar be hist[tp]. Calculate area of rectangle with hist[tp] as smallest bar. For hist[tp], the ‘left index’ is previous (previous to tp) item in stack and ‘right index’ is ‘i’ (current index).
3) If the stack is not empty, then one by one remove all bars from stack and do step 2.b for every removed bar.
但是3,我可以用哨兵去搞定。

这题目关键点：
1）一个栈里面到底存什么。
2）还有就是标兵了。

2.hash和two-pointer结合起来的算法
代表是leetcode的76题 Minimum Window Substring，这是求出在一个字符串中找到包含给定字符的最小长度。
这个算法结合了两点，一个是hash算法，还有一个就是两个指针算法。
我先给出代码
```
string minWindow(string s, string t) {
        vector<int> map(128,0);
        for(auto c: t) map[c]++;
        int counter=t.size(), begin=0, end=0, d=INT_MAX, head=0;
        while(end<s.size()){
            if(map[s[end++]]-->0) counter--; //in t
            while(counter==0){ //valid
                if(end-begin<d)  d=end-(head=begin);
                if(map[s[begin++]]++==0) counter++;  //make it invalid
            }  
        }
        return d==INT_MAX? "":s.substr(head, d);
    }

class Solution {
public:
    string minWindow(string s, string t) {
      vector<int> count(128,0);

      for(auto c:t)
	    count[c]++;
      
      int minl = INT_MAX;
      int counter = t.size();
      int fast,slow,head;
      
      head = slow = fast = 0;
      while (fast < s.size()) {
	if(count[s[fast++]]-- > 0) counter--;
	while (counter == 0) {
	  if (fast-slow < minl) {
	    minl = fast - slow;
	    head = slow;
	  }
	  if (count[s[slow++]]++ == 0) counter++;
	}
      }
      return minl == INT_MAX?"":s.substr(head,minl);
    }
};
```
下面我来详细解释一下。
首先，把目标字符先hash一下，和其他字符区分开来。
然后，用一个计算器来记录一共有多少字串，即长度counter。
还有两个指针，一个快指针，一个慢指针，也可以说是一个头指针，一个尾指针。
比如说这样一个例子。
aBabBbACddddABCaaaa 找出 ABC
这样一个例子。
运行时
1）第一次到C的时候减到0了。
2）然后运行这个循环，找开头了。如果这个字符串等于0.counter就需要++了。为什么呢？
因为非字符和重复的就已经小于0了，所以等于0的时候，counter++了， 就表示现在又要去后面找了。
所以说下面这两个循环非常厉害。
关键是这个
```
map[s[end++]]-- > 0 counter --
map[s[begin++]]++ == 0 counter ++
```
这是关键的技术点。
还有注意一下我这里没用map，而是用了一个vector。而且这里呢，这里字符不超过128,所以定义为128的长度就够了。
对于这样的问题，有着固定的套路。
对于在一个字符串找到一些限制的子字符串问题，我们有一个套路就是用一个hashmap加上two pointer，就这样。
```
int findSubstring(string s){
        vector<int> map(128,0);
        int counter; // check whether the substring is valid
        int begin=0, end=0; //two pointers, one point to tail and one  head
        int d; //the length of substring

        for() { /* initialize the hash map here */ }

        while(end<s.size()){

            if(map[s[end++]]-- ?){  /* modify counter here */ }

            while(/* counter condition */){ 
                 
                 /* update d here if finding minimum*/

                //increase begin to make it invalid/valid again
                
                if(map[s[begin++]]++ ?){ /*modify counter here*/ }
            }  

            /* update d here if finding maximum*/
        }
        return d;
  }
```

3.还有一道hash题目，是49题，这题比较好玩，很有典型代表。
```
class Solution {
public:
    vector<vector<string>> groupAnagrams(vector<string>& strs) {
      unordered_map<string,vector<string> > mp;
      vector<vector<string> > res;

      for (auto s : strs) {
	string t = s;
	sort(t.begin(),t.end());
	mp[t].push_back(s);
      }
      for (auto m :mp) {
	vector<string> temp(m.second.begin(),m.second.end());
	res.push_back(temp);
      }
      return res;
    }
};

```
这是个hash问题，很有代表性的问题。