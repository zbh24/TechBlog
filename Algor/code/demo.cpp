// find all the value
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
	a[i] = -1; // The deafult value is -1.
    }
}

// find the one
void try (int i) {
    int j;
    
    if(i >= N) {
        flag = true;
        count++;
        print();
        return;
    }
    for(j = 0;j < M; j++) { // The span
      if(flag == false) {
          a[i] = j;
	  if(check(i)) {
            if(i < N) { // The deep 
                try(i+1);
            }
	  }
	  if(flag == false)
	     a[i] = -1; // The deafult value is -1.
      }
    }
}

