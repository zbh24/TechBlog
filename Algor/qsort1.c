iint partition(int number[], int left, int right) { 
    int i = left - 1; 
    int j;
    for(j = left; j < right; j++) { 
        if(number[j] <= number[right]) { 
            i++; 
            SWAP(number[i], number[j]); 
        } 
    } 

    SWAP(number[i+1], number[right]); 
    return i+1; 
} 

void quickSort(int number[], int left, int right) { 
    if(left < right) { 
        int q = partition(number, left, right); 
        quickSort(number, left, q-1); 
        quickSort(number, q+1, right); 
    } 
} 

// This is a in-place algotithm
/*

QUICKSORT(A, p, r) 
    if p < r 
        then q <- PARTITION(A, p, r) 
                 QUICKSORT(A, p, q-1) 
                 QUICKSORT(A, q+1, r) 
end QUICKSORT 

PARTITION(A, p, r) 
    x <- A[r] 
    i <- p-1 
    for j <- p to r-1 
        do if A[j] <= x 
                 then  i <- i+1 
                         exchange A[i]<->A[j] 
    exchange A[i+1]<->A[r] 
    return i+1 
end PARTITION
  
 */
