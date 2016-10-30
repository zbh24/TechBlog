#include <iostream>
#include <vector>
#include <algorithm>
#include <string>
#include <sstream>
#include <cstdio>

using namespace std;

int split(string s,char c,vector<string>& res) {
  int start,end;
  int len;
  string temp;
  
  start = end = 0;
  len = s.length();
  while(end < len) {
    if(s[end] != c) {
      end++;
    } else {
      temp = s.substr(start,end-start);
      end++;
      start = end;
      res.push_back(temp);
    }
  }
  temp = s.substr(start,end-start);
  res.push_back(temp);
  return 0;
}

string  rev_char(string t) {
  string s = t;
  int i,j;
  char c;
  i = 0;
  j = s.length() -1;
  while (i < j) {
    c = s[i];
    s[i] = s[j];
    s[j] = c;
    i++;
    j--;
  }
  return s;
}


string rev(string str) {
  vector<string> temp;
  string res;
  string temp_s;
  split(str,' ',temp);
  for(int i = 0; i < temp.size();i++) {
    temp_s = rev_char(temp[i]);
    res += temp_s;
    if (i < temp.size()-1)
      res += " ";
  }
  return rev_char(res);
}

int main() {
  vector<string> input;
  vector<string> res;
  int n;
  string temp_s,t;
  cin >> n;
  //fflush();
  getchar();
  for (int i = 0;i < n;i++) {
    getline(cin,temp_s);
    input.push_back(temp_s);
  }
  for(int i = 0; i < input.size();i++) {
    temp_s = rev(input[i]);
    res.push_back(temp_s);
  }
  //string tmp1 = "Case #";
  stringstream tmp;
  for(int i = 0; i < res.size();i++) {
    //tmp << "Case #" << i <<": ";
    //cout << tmp.str();
    cout << "Case #"<<i+1<<": ";
    cout << res[i] << endl;
    //tmp ="";
  }
  return 0;
}
