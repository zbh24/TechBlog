#include <iostream>

using namespace std;

int father[MAX];
int rank[MAX];

void make_set(int x) {
  father[x] = x;
  rank[x] = 0;
}

// find ther root
int find_set(int x) {
  if (x != father[x]) {
    father[x] = find_set(father[x]);
  }
  return father[x];
}

void union(int x,int y) {
  int a = find_set(x);
  int b = find_set(y);
  if (a == b)
    return;
  if (rank[a] > rank[b])
    father[b] = a;
  
  else {
    if (rank[a] == rank[b])
      rank[b]++;
    father[a] = b;
  }
}
