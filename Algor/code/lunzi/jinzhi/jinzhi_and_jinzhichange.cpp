#include <iostream>

using namespace std;

int f(int n) {
   while ( n != 0) {
     int res;
     if (n >= 10000) {
       res +=n/10000;
       n = n % 10000;
     }
     if (n >= 1000) {
       res += n/1000;
       n = n % 1000;
     }
     if (n >= 100) {
       res += n/100;
       n = n % 100;
     }
     if (n >= 10) {
       res += n/10;
       n = n % 10;
     }
     res += n;
     return res;
   }
}

// This is shijinzhi,and from thee right to left
int f2(int n) {
  int res = 0;
  while (n != 0) {
    res += n % 10;
    n = n / 10;
  }
  return res;
}

int g(int n) {
  int res = 0;

  while (n != 0) {
    if (n % 2 == 1)
      res++;
    n = n / 2;
  }
  return res;
}

int main() {
  int n;
  int res = 0;
  while (cin >> n) {
    res = 0;
    for(int i = 1; i <= n;i++)
      if(f2(i) == g(i)) 
	res++;
    cout << res << endl;
  }
  return 0;
}
