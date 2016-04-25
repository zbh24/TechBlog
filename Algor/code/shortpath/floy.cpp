#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>
#include <iostream>
#include <string>
#include <set>
#include <vector>
#include <algorithm>
 
using namespace std;

#define maxvalue 100000
int A[1010][1010];
int path[1010][1010];


void init() {
  for(int i = 0;i < 1010;i++) {
    for(int j = 0;j < 1010;j++) {
	if(i != j)
	  A[i][j] = -1;
	else
	  A[i][j] = 0;
    }
  }
}

void floy(int n) {
  int i,j,k;

  //PS k must in the first loop
  for(k = 1;k <= n;k++)
    for(i = 1;i <= n;i++)
      for(j = 1;j <= n;j++) {
	if(i != j && k != i)
	  if(A[i][k] != -1 && A[k][j] != -1)
	    if(A[i][j] == -1 || (A[i][j] > A[i][k] + A[k][j]) )
	      A[i][j] = A[i][k] + A[k][j]; 
      }
  for(i = 1;i <= n;i++) {
    for(j = 1;j <n;j++)
      cout<<A[i][j]<< " ";
    cout<<A[i][j]<<endl;
  }
}

int input(int i,int j,int temp) {
  if(A[i][j] == -1 || temp < A[i][j]) {
    A[i][j] = A[j][i] = temp;
    return 0;
  }
  return 0;
}

int main() {
  int N,M;
  int i;
  int fst,snd,temp;

  cin>>N>>M;
  init();
  for(i = 0;i < M;i++) {
    cin>>fst>>snd>>temp;
    input(fst,snd,temp);
  }
  floy(N);
}




// 5 4

// 5 1 200
// 1 4 300
// 3 4 150
// 5 3 400
// 500

5 5 5 4
5 1 200
1 2 300
3 4 150
5 3 400
2 4 30
530
