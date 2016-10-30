void reverse(string s) {
  int i = 0;
  int j = s.length()-1;
  char c;
  for(;i < j;i++,j--) {
    c = s[j];
    s[j] = s[i];
    s[i] = c;
  }
  return;
}


def CycleBSearch(arr, val):
  left = 0
  right = len(arr) - 1
  while left <= right:
    mid = (left + right) / 2
    if val == arr[mid]:
      return mid          # found val

    if arr[left] <= arr[mid]:
      if arr[left] <= val < arr[mid]:
        right = mid - 1   # val is in left side
      else:
        left = mid + 1    # val is in right side
    else:
      if arr[left] > val > arr[mid]:
        left = mid + 1    # val is in right side
      else:
        right = mid - 1   # val is in left side
  return -1               # cannot find val



public static int FindMaxOfArray(int[] arr){
    int max = -1;
    int i = 0, j = arr.length - 1;
    int mid =(arr.length-1)/2;
    while(j - i > 1){
        //舍弃前半部分
        if(arr[mid] > arr[i] && arr[mid] > arr[j]){
            i = mid;
        }
        //舍弃后半部分
        else if(arr[mid] < arr[i] && arr[mid] < arr[j]){
            j = mid;
        }
        if(mid == (i+j)/2)
            break;
        mid = (i+j)/2;
    }
    if(arr[i] > arr[j])
        max = arr[i];
    else 
        max = arr[j];
    return max;
}
