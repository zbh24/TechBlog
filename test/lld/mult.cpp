#include<iostream>

using namespace std;

extern int add(int x, int y);
int multi(int x,int y) {
  int sum = 0;
  for (int i = 0; i < y; i++)
    sum += add(x, y);
  return sum;
}
