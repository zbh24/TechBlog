
int part(int A[],int low,int high) {
  int key = A[low];

  while(low < high) {
    while(low < high && A[high] >= key) {
      high--;
    }
    swap(A[low],A[high]);
    
    while(low < high && A[low] <= key) {
      low++;
    }
    swap(A[low],A[high]);
  }
  return low;
}

// because the shuzhou assian doesn;t need,so the change is can be this
// The first one is shuzhou

int part1(int A[],int low,int high) {
  int key = A[low];

  while(low < high) {
    while(low < high && A[high] >= key) {
      high--;
    }
    A[low] = A[high];
    while(low < high && A[low] <= key) {
      low++;
    }
    A[high] = A[low];
  }

  A[low] = key;
  return low;
}

void qsort(int A[],int low,int high) {
  int loc;  
  if(low < high) {
      loc = part(A,low,high);
      qsort(A,low,loc - 1);
      qsort(A,loc + 1,high);
  }
}


/*

对PARTITION和QUICKSORT所作的改动比较小。在新的划分过程中，我们在真正进行划分之前实现交换：
（其中PARTITION过程同快速排序伪代码（非随机））
RANDOMIZED-PARTITION(A，p，r)
1　i← RANDOM(p，r)
2　exchange A[r]←→A[i]
3　return PARTITION(A，p，r)
新的快速排序过程不再调用PARTITION，而是调用RANDOMIZED-PARTITION。
RANDOMIZED-QUICKSORT(A，p，r)
1　if p<r
2　then q← RANDOMIZED-PARTITION(A，p，r)
3　RANDOMIZED-QUICKSORT(A，p，q-1)
4　RANDOMIZED-QUICKSORT(A，q+1，r)[2] 

 */
