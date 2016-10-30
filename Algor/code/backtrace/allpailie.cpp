#include <iostream>
#include <vector>
#include <string>
#include <sstream>

using namespace std;

void dfs_int(vector<vector<int> >& res,vector<int>& temp,int cur,int len) {
  if (cur == len) {
    res.push_back(temp);
    return;
  }
  for(int i = 0;i < 10;i++) {
    temp.push_back(i);
    dfs_int(res,temp,cur+1,len);
    temp.pop_back();
  }
  return ;
}


void dfs_str(vector<string>& res,string& temp,int cur,int len) {
  if (cur == len) {
    res.push_back(temp);
    return;
  }
  for(int i = 0;i < 26;i++) {
    char c = 'A'+i;
    string t(1,c);
    t = temp + t;
    dfs_str(res,t,cur+1,len);
  }
  return ;
}

void dfs_mix(vector<string>& res,string& temp,int cur,int len) {
  if (cur == len) {
    res.push_back(temp);
    return;
  }
  for(int i = 0;i < 26+10;i++) {
    if (i < 26) {
      char c = 'A'+i;
      string t(1,c);
      t = temp + t;
      dfs_mix(res,t,cur+1,len);
    } else {
      stringstream t;
      t << temp << (i-26);
      string s = t.str();
      dfs_mix(res,s,cur+1,len);
    }
  }
  return ;
}


int main() {
  vector<vector<int> > res;
  vector<int> temp;
  //dfs_int(res,temp,0,6);
  for(int i = 0;i < res.size();i++) {
    for(int j = 0;j < res[i].size();j++) {
      cout << res[i][j];
    }
    cout << endl;
  }
  vector<string> str;
  string s;
  //dfs_str(str,s,0,5);
  dfs_mix(str,s,0,5);
  for(int i = 0;i < str.size();i++) {
    cout << str[i] << endl;
  }
  cout << endl;
  return 0;

}
