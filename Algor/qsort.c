
int part(int A[],int low,int high) {
  int key = A[low];

  while(low < high) {
    while(low < high && A[high] > key) {
      high--;
    }
    swap(A[low],A[high]);
    
    while(low < high && A[low] < key) {
      low++;
    }
    swap(A[low],A[high]);
  }
  return low;
}

void qsort(int A[],int low,int high) {
  int loc;  
  if(low < high) {
      loc = part(A[],low,high);
      qsort(A[],low,loc - 1);
      qsort(A[],loc + 1,high);
    }
}
