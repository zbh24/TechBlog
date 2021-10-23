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

vector<string> split(string s,char c) {
  int i;
  int k;
  int len;
  string temp;
  vector<string> res;

  k = i = 0;
  len = s.length();
  while(k < len) {
    if(s[k] != c) {
      k++;
    } else {
      temp = s.substr(i,k-i);
      k++;
      i = k;
      if (temp.length() > 0) {
        res.push_back(temp);
      }
    }
  }
  temp = s.substr(i,k-i);
  res.push_back(temp);
  return res;
}


vector<string> split1(string s,char c) {
  int i;
  int k;
  int len;
  string temp;
  vector<string> res;

  k = i = 0;
  len = s.length();
  while(k < len) {
    if(s[k] != c) {
      k++;
    } else {
      temp = s.substr(i,k-i);
      k++;
      i = k;
      if (temp.length() > 0) {
        res.push_back(temp);
      }
    }
  }
  temp = s.substr(i,k-i);
  res.push_back(temp);
  return res;
}


int main() {
  string s = "flower/world/////water//////hello";
  //cout<<s.substr(0,0) <<" "<<s.substr(0,0)<<endl;
  vector<string> res = split(s,'/');

  for(int i=0;i < res.size();i++)
    cout<<res[i]<<" "<< res[i].length()<<endl;

}
