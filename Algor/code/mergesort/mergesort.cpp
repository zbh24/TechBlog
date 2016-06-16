

// MOST fundmentaml
void merge1(int a[],int start,int mid,int end) {
  int first,second;
  int i;

  int res[] = new int;
  first = start;
  second = mid+1;
  i = 0;
  while (first <= mid && second <= end) {
    if (a[first] <= a[second]) {
      res[i++] = a[first];
      first++;
    } else {
      res[i++] = a[second];
      second++;
    }
  }
  if (first <= mid) {
    while (first <= mid)
      res[frist++] = a[i++];
  }
  if (second <= end) {
    while (second <= end)
      res[second++] = a[i++];
  }
  return res;
}

// If we want to mergt into the same array,we need to insert the a[] 
void merge1(int a[],int start,int mid,int end) {
  int first,second;
  int i;

  int res[] = new int;
  first = start;
  second = mid+1;
  i = 0;
  while (first <= mid && second <= end) {
    if (a[first] <= a[second]) {
      res[i++] = a[first];
      first++;
    } else {
      res[i++] = a[second];
      second++;
    }
  }
  if (first <= mid) {
    while (first <= mid)
      res[frist++] = a[i++];
  }
  if (second <= end) {
    while (second <= end)
      res[second++] = a[i++];
  }
  return res;
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
