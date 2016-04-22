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

struct trie {
  //char c;
  int flag;// -1 ,1,2
  int prity;
  struct trie *next[2];
};

typedef struct trie Trie;
Trie t[4000100];
int pos;
Trie *root;
bool rootflag;

int init(struct trie *t) {
  int i;

  for(i = 0 ;i < 2;i++) {
    t->next[i] = NULL;
  }
  t->flag = -1;
  t->prity = maxvalue;
  return 0;
}

int insert(int mask,string flag,int prity,string& ip) {
  int temp;
 
  Trie *current;
  current = root;
  if(mask == 0 && rootflag == true) {
    root->prity = prity;
    if(flag == "allow")
      root->flag = 1;
    else
      root->flag = 2;
    rootflag = false;
    return 0;
  } else if(mask == 0)
    return 0;

  for(int i = 0;i < mask;i++) {
    temp = ip[i] - '0';
   if(current->next[temp] == NULL) {
      Trie *nextnode = &t[pos++];
      init(nextnode);
      current->next[temp] = nextnode;
    }
    current = current->next[temp]; 
  }
  // the same node
  if(current->flag != -1) {
    return 0;
  }
  current->prity = prity;
  if(flag == "allow")
     current->flag = 1;
  else 
    current->flag = 2;  
  return 0;
}

string trans(string origin, int len = 32) {
    vector<string> ip;
    split(origin, '.', ip);
    string res = "";
    for (int i = 0; i < ip.size(); ++i) {
        int x = atoi(ip[i].c_str());
        res += ('0' + x/128);
        x = x%128;
        res += ('0' + x/64);
        x = x%64;
        res += ('0' + x/32);
        x = x%32;
        res += ('0' + x/16);
        x = x%16;
        res += ('0' + x/8);
        x = x%8;
        res += ('0' + x/4);
        x = x%4;
        res += ('0' + x/2);
        x = x%2;
        res += ('0' + x);
    }
    if (len != 32) {
        res = res.substr(0, len);
    }
    return res;
}

int pre(string flag,string addr,int prity) {
  int i;

  //vector<string> ip_addr;
  vector<string> ip_mask;
  string  ip;

  split(addr, '/',ip_mask);
  //split_int(ip_mask[0],'.',ip);

  if(ip_mask.size() == 1) {
    ip = trans(ip_mask[0]);
    insert(32,flag,prity,ip);
  } else {
    //ip = trans(ip_mask[0],stonum(ip_mask[1]));
    ip = trans(ip_mask[0],atoi(ip_mask[1].c_str()));
    insert(stonum(ip_mask[1]),flag,prity,ip);
  }
  return 0;
}


string get(string query) {
  int cur_prity;
  int cur_flag;
  string ip;
  Trie *current;
  
  ip = trans(query,32);
  current = root;
  cur_prity = maxvalue;
  cur_flag = -1;

  if(root->flag != -1) {
    cur_prity = root->prity;
    cur_flag = root->flag;
  }
  for(int i = 0;i < 32;i++) {
    int temp = ip[i] - '0';
    if(current->next[temp] != NULL) {
      if(current->next[temp]->flag == 1) {
	if(current->next[temp]->prity < cur_prity) {
	  cur_prity = current->next[temp]->prity;
	  cur_flag = 1; 
	}
      } else if(current->next[temp]->flag == 2) {
	if(current->next[temp]->prity < cur_prity) {
	  cur_prity = current->next[temp]->prity;
	  cur_flag = 2;
	}
      }
    } else {
      break;
    }
    current = current->next[temp];
  }
  if(cur_flag == -1)
    return "YES";
  else if(cur_flag == 1) {
    return "YES";
  }
  else {
    return "NO";
  }
}


int main() {
  int i;
  string flag;
  string addr;
  int N,M;
  string query;

  root = &t[0];
  pos++;
  init(root);
  rootflag = true;
  cin >> N >> M;
    for(i = 0; i < N;i++) {
      cin>>flag>>addr;
      pre(flag,addr,i);
    }    
    for(i = 0; i < M;i++) {
      cin >> query;
      cout<< get(query) << endl;
    }
  return 0;
}
