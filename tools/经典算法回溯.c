#经典算法回溯：深度搜索+剪枝
暴力破解法一般什么问题都能解决，但是你要是用这个来解决问题，基本上都不是正确答案，无论是空间还是时间上都很不理想。比如一个8皇后，它的空间树与有8的8次方这么大。所以，就考虑提前检测条件，如果不符合，就直接返回，不必尝试到最后一层，这样进行剪枝。（关键是：每进行一步，就检测条件，不返回符合，而不是把所有条件都填上才进行检测）。
回溯法的算法思想伪代码大概如下：

```
int a[n]; // 答案空间
void try(int i) {
    if(i >= n) // n代表深度，
       输出结果;
    else {
       for(j = 下界; j <= 上界; j=j+1)  // 枚举每个节点所有可能的选择
       {    a[i] = j;
            if(check(i))                 // 满足限界函数和约束条件
            {      best += a[i]; // 加上当前权值
                   try(i+1);  // 进入下一层
                   best -= a[i]; // 回溯前的清理工作
            }
        }
       
    }
}
```
一般的解题思路都是
1.先定义出问题的解空间，然后确定解空间树的结构。
2.定义出约束函数,有的时候还有界限函数，会进一步剪枝提高效率。
3.然后以深度优先方式搜索整个解空间树，找出所要的解。
下面附上我写的N皇后代码：
```
#include<stdio.h>
#include<stdlib.h>

int a[100];
int N; // backtrace‘s deep
int M; // backtrace's span
int count;

int print() {
    int i;
    printf("The %d's answer is:\n",count);
    for(i = 0;i < N;i++) {
        printf("%d ",a[i]);
    }
    printf("\n");
}

// evary time check the new add element with all the exists elements
int check(int i) {
    int j;
    for(j = 0;j < i;j++) { // The Vertif 
        if(a[i] == a[j] || abs(i-j) == abs(a[i]-a[j]))
            return 0;
    }
    return 1;
}

void try (int i) {
    int j;
    
    if(i >= N) {
        count++;
        print();
        return;
    }
    for(j = 0;j < M; j++) { // The span
        a[i] = j;
        if(check(i)) {
            if(i < N) { // The deep 
                try(i+1);
            }
        }
    }
    a[i] = -1; // The deafult value is -1.
}

void init() {
    int i;
    for(i = 0;i < 100;i++)
        a[i] = -1;
    count = 0;
}


int main(){
    int value;
    printf("Please input the number of the queue\n");
    scanf("%d",&value);
    M = N = value;
    init();
    try(0);
}
```
类似的问题还有素数环：
将从1到n这n个整数围成一个圆环，若其中任意2个相邻的数字相加，结果均为素数，那么这个环就成为素数环。
要求输出：从整数1开始。
代码如下：
```
#include<stdio.h>
#include<math.h>

int a[100];
int n;
int count;


int sushu(int i) {
    int k;

    for(k = 2;k <= sqrt(i);k++) {
        if(i%k == 0)
            return 0;
    }
    return 1;
}

int print() {
    int i;

    for(i=0;i< n;i++) {
        printf("%d ",a[i]);
    }
    printf("\n");
}

int check(int i) {
    int j;

    // 选出数字
    for(j = 0; j < i;j++) {
        if(a[i] == a[j]) {
            return 0;
        }
    }
    // 判断是否为素数
    if(i > 0 && i < n)
        if(!sushu(a[i]+a[i-1]))
            return 0;
    if(i == n-1)
        if(!sushu(a[i]+a[0]))
            return 0;
    return 1;
}

void try(i) {
    int j;

    if(i >= n) {
        count++;
        print();
        return;
    }
    for(j = 1; j <= n; j++) {
        a[i] = j;
        if(check(i)) {
            try(i+1);
        }
    }
}

int main() {
    scanf("%d",&n);
    try(0);
    printf("The answer is %d\n:",count);
}
```

旅行售货员问题(TSP问题)：某售货员要到若干城市去推销商品，一直各城市之间的路程，他要选定一条从驻地出发，经过每个城市一遍，最后回到住地的路线，使总的路程最短. 

设G=（V，E）是一个带权图。图中各边的权代表各城市间旅行费用。图的一条周游路线是包括V中的每个顶点在内的一条回路。周游路线的费用是这条路线上所有边的费用之和。旅行售货员问题就是要在图G中找出费用最小的周游路线。如下图所示是一个4顶点无向带权图。顶点序列1，2，4，3，l；1，3，2，4，1和1，4，3，2，1是该图中3条不同的周游路线。
解题思路：
使用回溯法寻找最小费用周游路线时，从解空间树的根结点A出发，搜索至B，C，F，L。在叶结点L处记录找到的周游路线1,2,3,4,1，该周游路线的费用为59。从叶结点L返回至最近活结点F处。由于F处已没有可扩展结点，算法又返回到结点C处。结点C成为新扩展结点，由新扩展结点，算法再移至结点G后又移至结点M，得到周游路线1，2，4，3，1，其费用为66。这个费用不比已有周游路线1，2，3，4，l的费用更小，因此，舍弃该结点。算法又依次返回至结点G，C，B。从结点B，算法继续搜索至结点D，H，N。在叶结点N处，相应的周游路线1，3，2，4，1的费用为25，它是当前找到的最好的一条周游路线。从结点N算法返回至结点H，D，然后从结点D开始继续向纵深搜索至结点O。依此方式算法继续遍历整个解空间，最终得到最小费用周游路线1，3，2，4，1。

还有0-1背包问题，除了用动态规划以外，也可以用回溯法来解决，因为放或者不放就是一种选择。

数字全排列(引用http://blog.csdn.net/daniel_ustc/article/details/17041933)
这里是用一个vis数组来表示是否访问过，而不是常用的swap操作，不过容易理解。
```
#include <stdio.h>

int a[10];
bool vis[10];
int n;//排列个数 n
void dfs(int dep)  //打印所有的全排列，穷举每一种方案
{
    if(dep == n)
    {
        for(int i = 0; i < n; i++)
        {
            printf("%d ",a[i]);
        }
        printf("\n");
        return ;
    }
    for(int i = 0; i < n; i++)// 找一个最小的未标记的数字，保证了字典序最小
    {
        if(!vis[i])
        {
            a[dep] = i+1;
            vis[i] = true;// 找到了就标记掉，继续下一层
            dfs(dep + 1);
            vis[i] = false;
        }
    }
}
int main()
{
    while(scanf("%d",&n) != EOF)
    {
        dfs(0);
    }
    return 0;
}
```
