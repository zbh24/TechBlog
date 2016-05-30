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

int c[1000][1000];

int lcs_len(string& x,int m,string& y,int n) {
  int i,j;

  for(i = 0;i < m;i++)
    c[i][0] = 0;

  for(j = 0;j < n;j++)
    c[0][j] = 0;
  
  for(i = 1;i < m;i++)
    for(j = 1;j < n; j++) {
      if(x[i] == y[j])
	c[i][j] = c[i-1][j-1] + 1;
      else
	c[i][j] = max(c[i-1][j],c[i][j-1]);
    }
  return 0;
}

int backtrack(string& x,int m,string& y,int n,string& res) {
  if (m < 0 || n < 0)
    return 0;
  else if (x[m] == y[n])
    return backtrack(x,m-1,y,n-1,res+=x[m]);

  else if (c[m][n-1] > c[m-1][n])
    return backtrack(x,m,y,n-1,res);
  else
    return backtrack(x,m-1,y,n,res);
}

void print(int m,int n) {
  for(int i = 0;i < m;i++) {
    for(int j = 0;j < n; j++)
      cout<<c[i][j]<<" ";
  cout<<endl;
  }
}

int main() {
  string s1 = "xddyssz";
  string s2 = "dsfsxdyzeeee";
  lcs_len(s1,s1.length(),s2,s2.length());
  print(s1.length(),s2.length());
  string res;
  backtrack(s1,s1.length(),s2,s2.length(),res);
  cout<<res<<endl;
}



