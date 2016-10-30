#include <iostream>
#include <string>
#include <vector>
#include <math.h>
#include <string.h>
#include <algorithm>

using namespace std;

int max(int a,int b) {
  return a>b?a:b;
}

int min(int a,int b) {
  return a<b?a:b;
}

int main() {
  int n;
  string s;
  int m ;
  cin >> n;
  cin >> s;
  cin >> m;
  string illpairs;

  bool illegal[26][26] ;

  for (int i=0; i < 26; i++) {
    for (int j=0; j < 26; j++) {
      illegal[i][j] = false;
    }
  }

  for (int i=0; i < m; i++) {
    cin >> illpairs;
    int k1 = illpairs[0] - 'a';
    int k2 = illpairs[1] - 'a';
    illegal[k1][k2] = true;
    illegal[k2][k1] = true;
  }
  int dp[n];
  memset(dp,0,sizeof(dp));

  dp[0] = 1;
  for(int i = 1;i < n;i++) {
    int temp = 1;
    char c = s[i] - 'a';
    for(int- j = i - 1;j >= 0;j--) {
      char c1 = s[j] - 'a';
      if(!illegal[c1][c])
	temp = max(temp,dp[j]+1);
    }
    dp[i] = temp;
  }
  int res = 0x7fffffff;
  for(int i = 0;i < n;i++)
    res = min(res,n-dp[i]);
  cout << res <<endl;
}
