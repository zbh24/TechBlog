#include <iostream>

using namespace std;


// This is shijinzhi,and from thee right to left
int f2(int n) {
  int res = 0;
  while (n != 0) {
    res += n % 10;
    n = n / 10;
  }
  return res;
}

int g1(int n) {
  int res = 0;

  while (n != 0) {
    if (n % 2 == 1)
      res++;
    n = n / 2;
  }
  return res;
}

int g2(int n) {
  int res = 0;
  while (n != 0) {
    res += n & 0x1;
    n = n >> 1;
  }
  return res;
}

int main() {
  int n;
  int res1,res2;
  while (cin >> n) {
    res1 = res2 = 0;
    res1 = g1(n);
    res2 = g2(n);
    cout << res1 <<" "<< res2 << endl;
  }
  return 0;
}
