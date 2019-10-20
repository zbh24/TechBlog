#include <iostream>

using namespace std;

int countNum;
int pre[1001];

// find the root
int find_set(int x) {
  int value = x;
  while (x != pre[x]) {
    x = pre[x];
  }
  // patch reduce
  int temp;
  while (pre[value] != x) {
    temp = pre[value];
    pre[value] = x;
    value = temp;
  }
  return x;
}

void union_set(int x,int y) {
  int a = find_set(x);
  int b = find_set(y);
  if (a == b) {
    return;
  } else {
    pre[a] = b;
    countNum--;
  }
}

int main() {
  int N, M;
  cin >> N;
  countNum = N;
  for (int i = 0; i < N;i++) {
    pre[i] = i;
  }
  cin >> M;
  for (int i = 0;i < M; i++) {
    int a, b;
    cin >> a >> b;
    union_set(a ,b);
  }
  std::cout << "res: " << countNum << std::endl;
}
