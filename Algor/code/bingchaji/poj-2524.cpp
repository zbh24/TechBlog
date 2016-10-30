#include <iostream>
#include <vector>
#include <string>
#include <map>

using namespace std;

#define MAX 100010

int father[MAX];
int rank_node[MAX];
int count;

void mark_set(int x) {
  father[x] = x;
  rank_node[x] = 0;
}

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
  if (rank_node[a] > rank_node[b])
    father[b] = a;
  
  else {
    if (rank_node[a] == rank_node[b])
      rank_node[b]++;
    father[a] = b;
  }sl
  count--;
}

int main() {
  int n,m;
  int order = 1;
  while (cin >> n >> m) {
    if (n == 0 && m == 0)
      break;

    count = n;
    for(int i = 1;i <= n;i++)
      mark_set(i);
    
    int f,s;
    for(int j = 0; j < m;j++) {
      cin >> f >> s;
	union_set(f,s);
    }
    cout << "Case " <<order++ <<": " << count << endl;
  }
  return 0;
}
