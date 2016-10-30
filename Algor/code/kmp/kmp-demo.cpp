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

int next[100];


int gennext(string s) {
  int len = s.length();
  int k,j;

  j = 0;
  k = -1;
  next[0] = -1;
  
  while(j < len -1) {
    if(k == -1 || s[j] == s[k]) {
      k++;
      j++;
      next[j] = k;
    } else {
      k = next[k];
    }
  } 
  return 0;
}

int kmp(string s1,int len1,string s2,int len2) {
  int i,j;

  i = j = 0;
  while (i < len1 && j < len2) {
    if(j == -1 || s1[i] == s2[j]) {
      i++;
      j++;
    } else {
      j = next[j];
    }
  }
  if (j == len2)
    return i - j;
  else
    return -1;
}



int main() {
  string s1 = "zhangssdzdsgfszbssgsgsgsagzsdbzbhwsgqweq";
  string s2 = "zbhw";
  gennext(s2);
  cout<<kmp(s1,s1.length(),s2,s2.length())<<endl;
}
