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


//dp[i][j]:表示s1的前i个字符和s2的前j个字符中最多有多少相同的
int dp[100][100];

int lcs(string& s1,string& s2) {
  int len1,len2;

  len1 = s1.length();
  len2 = s2.length();

  for(int i=0;i < len1;i++)
    dp[i][0] = 0;

  for(int j=0;j < len2;j++)
    dp[0][j] = 0;


  for(int i=1;i <= len1;i++)
    for(int j=1;j <= len2;j++) {
      if(s1[i] == s2[j])
	dp[i][j] = dp[i-1][j-1] +1;
      else 
	dp[i][j] = max(dp[i-1][j],dp[i][j-1]);
    }

  return dp[len1][len2];
}


int main() {

  string s1,s2;

  while(cin >> s1 >> s2) {
    
    cout<<lcs(s1,s2)<<endl;

  }
  return 0;
}
