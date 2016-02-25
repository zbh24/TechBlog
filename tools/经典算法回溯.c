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
            if(check(j))                 // 满足限界函数和约束条件
            {     
                   try(i+1);  // 进入下一层
            }
        }
        a[i] = -1; // 回溯前的清理工作（如a[i]置空值等）;
    }
}
```
一般的解题思路都是
1.先定义出解空间树。
2.定义出约束函数,有的时候还有界限函数，会进一步剪枝提高效率。
3.然后按照上面的框架进行求解。
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

旅行售货员问题：
设G=（V，E）是一个带权图。图中各边的权代表各城市间旅行费用。图的一条周游路线是包括V中的每个顶点在内的一条回路。周游路线的费用是这条路线上所有边的费用之和。旅行售货员问题就是要在图G中找出费用最小的周游路线。如下图所示是一个4顶点无向带权图。顶点序列1，2，4，3，l；1，3，2，4，1和1，4，3，2，1是该图中3条不同的周游路线。
