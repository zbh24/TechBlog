#include <stdio.h>


int fun(int a,int b) {
  int temp = a + 1;
  return temp+b;

}
int main() {
  int a,b;
  a = 3;
  b = 4;
  int c;
  c = fun(a,b);
  printf("%d\n",c);
  return 0;
}
