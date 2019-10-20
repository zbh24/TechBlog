#include<iostream>
#include<vector>
using namespace std;

int countNum;
int pre[201];

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

int findCircleNum(vector<vector<int> >& M) {
  countNum = M[0].size();
  int numSize = countNum;
  for (int i = 0; i < countNum; i++) {
    pre[i] = i;
  }
  for (int i = 0; i < numSize; i++) {
    vector<int> &temp = M[i];
    for (int j = 0; j < temp.size(); j++) {
      if (temp[j] == 1)
	union_set(i, j);
    }
  }
  return countNum;
}
