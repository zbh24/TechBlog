#include <iostream>
#include <vector>
#include <algorithm>


using namespace std;

#define MAX 1000

int father[MAX];
int rank[MAX];

void mark_set(int x) {
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

void union_set(int x,int y) {
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

bool is_same_union(int x,int y) {
  return find_set(x) == find_set(y);
}

int main() {
  int num,num_of_union;
  cin >> num >> num_of_union;
  char temp;
  for(int i = 1;i <= num;i++) {
    mark_set('a'+i-1);
  }
  
  char first,second;
  for(int i = 0;i < num_of_union;i++) {
    cin >> first >> second;
    union_set(first,second);
  }
  
  for(int i = 0;i < 10;i++) {
    cin >> first >> second;
    cout << first << " and " << second << ":" << is_same_union(first,second)<<endl;
  }
  return 0;
}
