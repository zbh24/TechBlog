#include<stdio.h>
#include<math.h>

int a[100];
int n;
int count;

int prim[20] = {1,3,5,7,11,13,17,19,23,29,31,37};  

int sushu(int i) {
    int k;

    for(k = 0;k < 12;k++) {
        if(i == prim[k])
            return 1;
    }
    return 0;
}

int print() {
    int i;
    
    printf("%d",a[0]);
    for(i=1;i< n;i++) {
        printf(" %d",a[i]);
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
    if(i < n)
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
        print();
        return;
    }
    if(i%2 == 1) {
        j = 2;
    } else {
        j = 3;
    }
    for(;j <= n;j=j+2) {
        a[i] = j;
        if(check(i)) {
            try(i+1);
        }
    }
}

int main() {
    a[0] = 1;
    while(scanf("%d",&n) != EOF) {
        count++;
        printf("Case %d:\n",count);
        if(n == 1) {
            print();
        } else if(n%2 == 1) {
        } else { 
            try(1);
        }
        printf("\n");
    }
}
