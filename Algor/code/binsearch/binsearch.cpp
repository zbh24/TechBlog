// find the key
int binsearch(int A[],int low ,int high,int key) {

  int mid; 
  while(low <= high) {
    mid = (low + high) / 2;
    if(A[mid] > key)
      high = mid - 1;
    else if(A[mid] < key)
      low = mid + 1;
    else
      return mid;
  }
  return -1;
}

// find the closet key
// the mircros question
int binsearch(int A[],int low ,int high,int key) {

  int mid; 
  int value;
  int max_mid;
  int max_value;

  max_mid = max_value = 0;
  while(low <= high) {
    mid = (low + high) / 2;
    value = dosomething(A[mid]);

    if(value > key)
      high = mid - 1;
    else if(value < key) {
      if(abs(value-key) < abs(maxvalue-key)) {
	max_mid = mid;
	max_value = value;
      }
      low = mid +1;
    } else if(value == key) {
	max_mid = mid;
	max_value = value;
	break;
      }
  }
  return 0;
}
