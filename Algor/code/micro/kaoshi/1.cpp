#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>
#include <iostream>
#include <string>
#include <set>
#include <vector>
#include <algorithm>
#include <map>
#include <sstream>
#include <queue>

using namespace std;

#define SIZE 1000010
long long d[SIZE] = {0};

int compute(int len) {
  bool f1,f2;
  f1 = f2 = false;

  int first,second,f_pos,s_pos;
  bool flag = false;
  
  while (!flag) {
    flag = true;
    first = second = 0;
    f_pos = s_pos = 0;
    f1 = f2 = false;
    
    for(int i = 1;i <= len;i++) {
      if(d[i] != -1 && f1 == false) {
	first = d[i];
	f_pos = i;
	f1 = true;
	continue;
      }
      if(d[i] != -1 && f2 == false) {
	second = d[i];
	s_pos = i;
	f2 = true;
      }
      if(f1 == true && f2 == true) {
	if( (first + second) % 2 == 1) {
	  d[f_pos] = -1;
	  d[s_pos] = -1;
	  flag = false;
	  f1 = false;
	  f2 = false;
	} else {
	  f2 = false;
	}
      }
    }
  }
  int result;
  int temp = 0;
  for(int i =1;i <= len;i++)
    if(d[i] == -1)
      temp++;
  return len-temp;
}

int main() {
  int N;
  cin >> N;
  for(int i = 1;i <= N;i++)
    cin >> d[i];
  cout << compute(N) <<endl;
  
  return 0;
}
