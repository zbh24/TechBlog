#include <iostream>
#include <vector>
#include <math.h>

using namespace std;


int first(vector<int> &num) {
  int size = num.size();
  int res = 0;
  for(int i = 0; i < size;i++) {
    res += num[i] * pow (10,size-i-1);
  }
  return res;
}

int second(vector<int> &num) {
  int res = 0;
  for(int i = 0;i < num.size();i++) {
      res = res * 10 + num[i];
  }
  return res;
}


int main() {
  int n;
  vector<int> num;
  int res1 , res2;
  res1 = res2 = 0;
  int temp = 0;
  while (cin >> n) {
    num.clear();
    for(int i = 1; i <= n;i++) {
      cin >> temp;
      num.push_back(temp);
    }
    res1 = first(num);
    res2 = second(num);
    cout << res1 <<" "<< res2 << endl;
  }
  return 0;
}
