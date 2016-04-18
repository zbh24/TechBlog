#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>
#include <iostream>
#include <string>
#include <set>
#include <vector>
#include <algorithm>
#include <sstream>
#include <stack>

using namespace std;

class Solution {
public:

  int length;
  vector<string> res;

  int dfs(int i, string tmp,int left,int right) {
    int j;

    if(i >= length * 2) {
      res.push_back(tmp);
      return 0;
    }
    if(left > length || right > length)
      return 0;

      if(left >= right) {
	// tmp += '(';
	 dfs(i+1,tmp+'(',left+1,right);
	 //dfs(i+1,tmp,left+1,right);
      }
      else {
	  return 0;
      }
      //tmp = tmp.substr(0,tmp.length()-1);
  
      if(right >= left)
	  return 0;
      else {
	//tmp += ')';
          dfs(i+1,tmp+')',left,right+1);
	//dfs(i+1,tmp,left+1,right);
      }
      //tmp = tmp.substr(0,tmp.length()-1);
          

    return 0;
  }

   bool isValid(string s) {
      int len;
      int i;
      stack<int> st;
      int tmp;

      len = s.length();
      i = 0;
      while(i < len) {
	if(s[i] == '(' )
	  st.push(s[i]);
	else if(s[i] == ')') {
	  if(st.empty())
	    return false;
	  tmp = st.top(); 
	  st.pop();
	  if((s[i] - tmp) != 1) 
	    return false;
	}
	i++;
      }
      if(st.empty())
	return true;
      else
	return false;
    }

    vector<string> generateParenthesis(int n) {
      string tmp;
      int i;
      length = n;
      dfs(0,tmp,0,0);
      vector<string>::iterator it;
      it = res.begin();

      while(it != res.end()) {
      	if(!isValid(*it)) {
      	  res.erase(it);
        }
        else
      	  it++;
      }
      return res;
    }
};

int main() {
  Solution s1;
  vector<string> result;

  int i;
  result = s1.generateParenthesis(3);
  for(i = 0;i < result.size();i ++)
    cout<<result[i]<<endl;

}
