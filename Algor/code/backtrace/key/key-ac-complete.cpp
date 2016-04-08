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


int martx[10][10] = {
                    {1,0,0,0,0,0,0,0,0,0}, //0
		    {1,1,1,1,1,1,1,1,1,1}, //1
		    {1,0,1,1,0,1,1,0,1,1}, //2
		    {0,0,0,1,0,0,1,0,0,1}, //3
		    {1,0,0,0,1,1,1,1,1,1}, //4
		    {1,0,0,0,0,1,1,0,1,1}, //5
		    {0,0,0,0,0,0,1,0,0,1}, //6
		    {1,0,0,0,0,0,0,1,1,1}, //7
		    {1,0,0,0,0,0,0,0,1,1}, //8
		    {0,0,0,0,0,0,0,0,0,1}  //9
};

string s;
vector<int> value;
vector<int> res;
int length;
int flag;

int look_less(int k,int less) {
  int i;

  for(i = 9; i >= 0;i--) {
    if(martx[k][i] == 1 && i < less)
      return i;
  }
  return -1;
}


bool cmp(vector<int>& x,vector<int>& y) {
  int len = min(x.size(),y.size());
  int i;

  for(i = 0;i < len;i ++)
    if(x[i] == y[i])
      continue;
    else if(x[i] < y[i])
      return true;
    else 
      return false;
  return true;
}


int change() {
  int i;

  // cout <<"legnh" << s.length() <<endl;
  for(i = 0;i<s.length();i++)
    value.push_back((s[i] -'0'));
  return 0;
}

int dfs(int i ,int key,int next) {
  int j;
  int temp;

  if(cmp(res,value) == false)
    return 0;

  if(i >= length) {
      flag = true;
      return 0;
  }

  for(j = next; j >= 0 ;) {
    if(flag == false) {
      res.push_back(j);
      dfs(i+1,j,look_less(j,10));
      if(flag == false)
	res.pop_back();
    }
    temp = look_less(key,j);
    if(temp != -1) 
      j = temp;
    else
      break;
  }
  return 0;
}

int getvalue() {
  int i,j;
  int first_value;

  // initioliza
  value.clear();
  res.clear();
  flag = false;
  change();

  length =  value.size();
  if(length == 1) {
    res = value;
    return 0;
  }
  res.push_back(value[0]);
  dfs(1,value[0],look_less(value[0],10));
  if(flag == false) {
    res.pop_back();
    res.push_back(value[0]-1);
    dfs(1,value[0]-1,look_less(value[0],10));
  }
  return 0;
}




int main() {
  int n;
  int i;
  vector<int> ::iterator it;

  while(cin>>n) {
    for(i = 0;i < n ;i++) {
      cin >> s ;
      getvalue();
      it = res.begin();
      while(it != res.end()) {
	cout <<*it;
	it++;
      }
      cout << endl;
    }
  }
  return 0;
}



