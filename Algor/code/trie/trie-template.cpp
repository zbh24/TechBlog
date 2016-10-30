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

struct trie {
  char c;
  int count;
  struct trie *next[26];
};

typedef struct trie Trie;
Trie t[1000010];
int pos;
int temp;
Trie *root;
Trie *current;


int init(struct trie *t) {
  int i;

  for(i = 0 ;i < 26;i++) {
    t->next[i] = NULL;
  }
  return 0;
}


int insert(string s) {
  int len;
  int temp;
  len = s.length();

  for(int i = 0;i < len;i++) {
    temp = s[i] - 'a';
    if(current->next[temp] == NULL) {
      Trie *nextnode = &t[pos++];
      nextnode->c = s[i];
      nextnode->count = 1;
      init(nextnode);
      current->next[temp] = nextnode;
    } else {
      current->next[temp]->count++;
    }
    current = current->next[temp]; 
  }
  return 0;
}

int find(string s) {
  int len = s.length();
  int temp;
  Trie *start = root;

  for(int i = 0;i < len;i++) {
    temp = s[i] - 'a';
    if(start->next[temp] == NULL)
      return 0;
    start = start->next[temp];
  }
  return start->count;
}


int main() {
  string tmp;
  int n,m;

  root = &t[0];
  init(root);
  pos = 1;
  cin>>n;
  for(int i = 0;i < n;i++) {
    cin>>tmp;
    current = root;
    insert(tmp);
  }

  cin>>m;
  for(int i = 0;i < m;i++) {
    cin>>tmp;
    cout<<find(tmp)<<endl;
  }

  return 0;
}
