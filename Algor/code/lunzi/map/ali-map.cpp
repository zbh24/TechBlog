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

vector<string> pre(string s) {
  int i;
  int k;
  int len;
  string temp;
  vector<string> res;
  
  k = i = 0;
  len = s.length();
  while(k < len) {
    if(s[k] != ' ') {
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
  return res;
}


// vector<double> BatchQueryExecutionTime(const vector<string>&sqls, const vector<double>&times, const vector<string>&keywords) {
//   int len1,len2;

//   len1 = sqls.size();
//   len2 = keywords.size();
//   set<string,float> res;
//   set<string,float>::iterator it;
//   vector<string> input;
//   vector<double> count;
//   //set<string,double,int> 

//   for(int i = 0;i < len1 ;i++) {
//     input = pre(sqls[i]);
//     for(int j = 0;j < input.size();j++) {
//       it = res.find(input[j]);
//       if(it != res.end()) {
// 	float x = (*it)[1];
// 	x = (x + times[i]) / 2;
// 	res.erase(input[j]);
// 	res.insert(input[j],x);
//       } else {
// 	res.insert(input[j],times[i]);
//       }
//     }
//   }

//   for(int i;i < len2;i++) {
//     it = res.find(keywords[i]);
//     count.push_back((*it)[1]);
//   }
//   return count;
// }


// vector<double> BatchQueryExecutionTime(const vector<string>&sqls, const vector<double>&times, const vector<string>&keywords) {
//   int len1,len2;

//   len1 = sqls.size();
//   len2 = keywords.size();
//   set<string,float> res;
//   set<string,float>::iterator it;
//   vector<string> input;
//   vector<double> count;
//   //set<string,double,int> 

//   for(int i = 0;i < len1 ;i++) {
//     input = pre(sqls[i]);
//     for(int j = 0;j < input.size();j++) {
//       it = res.find(input[j]);
//       if(it != res.end()) {
// 	float x = (*it)[1];
// 	x = (x + times[i]) / 2;
// 	res.erase(input[j]);
// 	res.insert(input[j],x);
//       } else {
// 	res.insert(input[j],times[i]);
//       }
//     }
//   }

//   for(int i;i < len2;i++) {
//     it = res.find(keywords[i]);
//     count.push_back((*it)[1]);
//   }
//   return count;
// }


struct key {
  double t;
  int count;
};
typedef struct key E; 
map<string s,E> res;
map<string s,E>::iterator it;
 
int BatchQueryExecutionTime(const vector<string>&sqls, const vector<double>&times, const vector<string>&keywords) {
  int len1 = sqls.size();
  int len2 = keywords.size();
  vector<string> temp;
  
  for(int i =0 ;i < len1 ;i++) {
    temp = pre(sqls[i]);
    for(int j = 0;j < temp.size();j++) {
      it = res.find(temp[j]);
      if(it == res.end()) {
	E x;
	x.t = times[i];
	x.count = 1;
	res.insert(pair<string,int>(temp[j],x));
      } else {
	E y;
	y.t = it->second.t + times[i];
	y.count = it->second.count + 1;
	res.erase(it);
	res.insert(temp[j],y);
      }
    }
  }

  for(int i = 0;i < len2 ;i++) {
    string s = keywords[i];
    it = res.find(s);
    if(it != res.end()) {
      cout << (*it->second.t) /(*it->second.count)<<endl;
    } else {
      cout<<0<<endl;
    }
  }
  return 0;
}

int main() {
  string s = "ok";

  vector<string> res = pre(s);

  for(int i=0;i < res.size();i++)
    cout<<res[i]<<" "<< res[i].length()<<endl;

}
