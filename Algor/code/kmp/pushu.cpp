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

int pipei(string s1,int len1,string s2,int len2) {

  int i,j,k;

  for(i = 0;i < len1;i++) {
    k = i;
    for(j = 0;j < len2;j++) {
      if(s1[k] == s2[j]) {
	k++;
      } else {
	break;
      }
    }
    if(j == len2)
      return i;
  }
  return -1;
}

int main() {
  string s1 = "zhangssdzdsgfszbssgsgsgsagzsdbzbhwsgqweq";
  string s2 = "zbhw";
  
  cout<<pipei(s1,s1.length(),s2,s2.length())<<endl;
}
