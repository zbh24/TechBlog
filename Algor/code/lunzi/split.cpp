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
 
using namespace std;

#define maxvalue 1000000

int stonum(const string &text)
{
     istringstream ss(text);
     int result;
     return ss >> result ? result : 0;
}

int  split_int(string s,char c,vector<int>& res) {
  int i;
  int k;
  int len;
  string temp;
  //vector<int> res;
  int x;

  k = i = 0;
  len = s.length();
  while(k < len) {
    if(s[k] != c) {
      k++;
    } else {
      temp = s.substr(i,k-i);
      k++;
      i = k;
      x = stonum(temp);
      res.push_back(x);
    }
  }
  temp = s.substr(i,k-i);
  x = stonum(temp);
  res.push_back(x);
  return 0;
}

int split(string s,char c,vector<string>& res) {
  int i;
  int k;
  int len;
  string temp;
  //vector<string> res;

  k = i = 0;
  len = s.length();
  while(k < len) {
    if(s[k] != c) {
      k++;
    } else {
      temp = s.substr(i,k-i);
      k++;
      i = k;
      res.push_back(temp);
    }
  }
  temp = s.substr(i,k-i);
  res.push_back(temp);
  return 0;
}


int main() {

}
