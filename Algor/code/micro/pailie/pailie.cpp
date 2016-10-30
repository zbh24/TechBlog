#include <iostream>
#include <string>
#include <vector>

using namespace std;

void  dfs(vector<string>& res,string& temp,int& cur_len,int& len) {
  if (cur_len > len)
    return;
  
  if (cur_len == len) {
    res.push_back(temp);
    return;
  }
  for(int i = 0;i < 26;i++) {
    cur_len++;
    char c= 'a'+i;
    string t = temp+c;
    dfs(res,t,cur_len,len);
    cur_len--;
  }
}

int main() {
  vector<string> res;
  string temp;
  int num;
  cin >> num;
  int i = 0;
  dfs(res,temp,i,num);
  for(int i = 0;i < res.size();i++)
    cout << res[i] <<endl;
  
  return 0;
}
