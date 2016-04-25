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

int A[1010][1010];
int B[1010];
int from[1010];

// -1 represtents extremely big
void init() {
  for(int i = 0;i < 1010;i++) {
    for(int j = 0;j < 1010;j++)
	A[i][j] = -1;
    B[i] = -1;
  }
}

int printpath(int src,int n) {
  int i;
  int temp;

  while(src != n) {
    cout<<n<< " ";
    n = from[n];
  }
  cout<<src<<endl;
}

int dij(int n,int src,int dst) {
  vector<int> orign;
  int cur_dis,cur_node;
  int start;
  vector<int>::iterator it;
  
  for(int i = 1;i <= n;i++)
    if(i != src)
      orign.push_back(i);
  
  cur_dis = 0;
  cur_node = src;
  start = src;
  it = orign.begin();
  from[start] = start;
  
  while(orign.size() != 0) {
    it = orign.begin();
    while(it != orign.end()) {
      int node = *it;
      if(A[start][node] != -1)
	if(B[node] == -1) {
	  B[node] = A[start][node] + cur_dis;
	  from[node] = start;
	} else if(A[start][node] + cur_dis < B[node]) {
	  B[node] = A[start][node] + cur_dis;
	  from[node] = start;
	}
      
      it++;
    }

    int temp;
    it = orign.begin();
    while(B[*it] == -1)
      it++;
    temp = B[*it];
    cur_node = *it;

    while(it != orign.end()) {
      if(B[*it] < temp && B[*it] != -1) {
	temp = B[*it];
	cur_node = *it;
      }
      it++;
    }
    cur_dis = temp; 
    if(cur_node == dst) {
      printpath(src,dst);
      return cur_dis;
    }
    start = cur_node;
    it = find(orign.begin(),orign.end(),cur_node);
    orign.erase(it);
  } 
  printpath(src,dst);
  return B[dst];
}


int input(int i,int j,int temp) {
  if(A[i][j] == -1 || temp < A[i][j]) {
    A[i][j] = A[j][i] = temp;
    return 0;
  }
}

int main() {
  int N,M,S,T;
  int i;
  int fst,snd,temp;

  cin>>N>>M>>S>>T;
  init();
  for(i = 0;i < M;i++) {
    cin>>fst>>snd>>temp;
    input(fst,snd,temp);
  }
  cout<<dij(N,S,T)<<endl;
}
