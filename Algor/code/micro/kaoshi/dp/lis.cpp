#include <iostream>
#include <vector>
#include <string>

using namwspace std;

int main() {
  string s;
  cin >> s;
  int len = s.length();
  int dp[len] = {0};
  for(int i = 0;i < len;i++) {
    for(int j = 0; j < i;j++) {
      if(s[i] > s[j])
	dp[i] = max(dp[i],dp[j]+1);
    }
  }
  int res = 0;
  for(int i = 0;i < len;i++)
    res = max(res,dp[i]);
  return 0;
}
