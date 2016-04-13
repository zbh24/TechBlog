#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>
#include <iostream>
#include <string>
#include <set>
#include <vector>
#include <algorithm>
 
using namespace std;


int dp[100];

int dap(int n) {
  int MIN;
  int i,j;

  dp[0] = 0;
  dp[1] = dp[3] =dp[5]  = 1;
  for(i = 1;i <= n;i++) {
    if(i != 1 && i != 5 && i != 10 && i != 20 && i != 50 && i != 100) {
      MIN = dp[i-1] + 1;
      for(j = 1;j < i; j++)
	MIN = min((dp[i-j]+dp[j]),MIN);
      dp[i] = MIN;
    } else
      dp[i] = 1;
  }
  return dp[n];
}

int main() {
  int m;


  while(cin >> m) {
    
    cout<<dap(m) << endl;
  }
}
