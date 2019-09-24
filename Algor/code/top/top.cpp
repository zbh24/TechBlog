#include<iostream>
#include<string>
#include<vector>
#include<set>
#include<map>
using namespace std;

int main() {
  string str;
  typedef std::pair<int,int> Loc;
  typedef std::set<Loc> Set; 
  map<int,Set> res; 
   
  cin >> str;
  bool dotFlag  = false;
  int start,end, lastDotLoc;
  bool startFlag = false;
  int i = 0;
  for (i = 0; i < str.size(); i++) {
    if ((str[i] >= '0' && str[i] <= '9') || str[i] == '.') {
      if (str[i] >= '0' && str[i] <= '9') {
        if (startFlag == false) {
	  startFlag = true;
	  start = i;
	}
      } else if (str[i] == '.') {
        if (dotFlag == false) {
          dotFlag = true;
	  lastDotLoc = i;
	  startFlag = true;
	} else {
	  Loc temp(start , i-1);
          start = lastDotLoc + 1;             
	  res[i -1 - start + 1].insert(temp);
	}
      }
    } else {
      if (startFlag == true) {
        startFlag = false;
        dotFlag = false;
	Loc temp(start, i-1);
	res[i -1 - start + 1].insert(temp);
      }
    }
  }
  i--;
  if ((str[i] >= '0' && str[i] <= '9')) {
    Loc temp(start , i-1);
    res[i - start + 1].insert(temp);
  }
  return 1;
}
//abcd213.7546.809.561
