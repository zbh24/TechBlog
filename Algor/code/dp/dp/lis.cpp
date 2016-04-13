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


// longest increasing sequence


vector<int> input;
vector<int> res;
int dp[100];
int count;

//dp[i]:
//in the first n element,the lis is i:
//so the transformis :
//if(a[i] > a[i-1] then dp[i-1] + 1 else max(dp[i-1],1)
int lis() {
  int len;
  int i,j;
  int temp;
  
  len = input.size();
  for(i = 0;i < len ;i++) {
    temp = 1;
    for(j = 0;j < i;j ++)
      if(input[i] >= input[j]) {
	temp = max(temp,dp[j] + 1);
      }
    dp[i] = temp;
  }
  return 0;
}


int main() {
  int n;
  int i;
  int temp;

  while(cin >> n) {
    input.clear();
    for(i = 0; i < n; i++) {
      cin >> temp;
      input.push_back(temp);
    }
    lis();
    sort(dp,dp + n);
    cout<<dp[n-1]<<endl;
  } 
}
