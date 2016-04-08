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
        if(a[i] == a[j])
            return 0;
    }
    for(j = 0;j < i;j++) {
        if(abs(i-j) == abs(a[i]-a[j]))
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
