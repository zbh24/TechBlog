

void merge(int a[],int start,int mid,int end) {


}



void mergesort(int a[],int start,int end) {
  int mid;
  if (start < end) {
    mid = (start+end) / 2;
    mergesort(a,start,mid);
    mergesort(a,mid+1,end);
    merge(a,start,mid,end);
  }
}
