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
  int dp[n][26];
  memset(dp,0,sizeof(dp));

  dp[0][s[0]-'a'] = 1;

  for (int i=1; i < n; i++) {
    char c = s[i];
    
    for (char c1='a'; c1 <= 'z'; c1++) {
      dp[i][c1-'a'] = dp[i-1][c1-'a'];
    }
    for (char c1='a'; c1 <= 'z'; c1++) {
      if (!illegal[c1-'a'][c-'a']) {
	dp[i][c-'a'] = max(dp[i][c-'a'], dp[i-1][c1-'a']+1);
      }
    }
  }
  int res = 0x7fffffff;
  for (int i=0; i < 26; i++) {
    res = min(res, n - dp[n-1][i]);
  }
  cout << res << endl;
  return 0;
}
