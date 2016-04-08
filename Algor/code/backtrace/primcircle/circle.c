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
