#include <iostream>
#include <vector>
#include <string>
#include <map>

using namespace std;

#define MAX 100010

int father[MAX];
int rank_node[MAX];

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
  }
}

int main() {
  int num,group;
  while (cin >> num >> group) {
    if (num == 0 && group == 0)
      break;
    for(int i = 0;i < num;i++)
      mark_set(i);
    for(int k = 0; k < group;k++) {
      int count,first,temp;
      cin >> count >> first;
      for(int j = 1; j < count;j++) {
	cin >> temp;
	union_set(first,temp);
      }
    }
    int result = 0;
    for(int i = 0;i < num;i++)
      if (find_set(0) == find_set(i))
	result++;
    cout << result <<endl;
  }
  return 0;
}
