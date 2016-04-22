#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>
#include <iostream>
#include <string>
#include <set>
#include <vector>
#include <algorithm>
#include <queue>

using namespace std;

struct trie {
  char c;
  struct trie *next[26];
  struct trie *hou;
  bool flag_own;
  bool flag_hou;
};

typedef struct trie Trie;
Trie t[1000010];
int pos;
Trie *root;

int init(struct trie *t) {
  int i;

  for(i = 0 ;i < 26;i++) {
    t->next[i] = NULL;
  }
  t->flag_own = false;
  t->flag_hou = false;
  return 0;
}


//First step:Trie tree
int insert(string s) {
  int len;
  int temp;
  len = s.length();

  Trie *current;
  current = root;
  for(int i = 0;i < len;i++) {
    temp = s[i] - 'a';
    if(current->next[temp] == NULL) {
      Trie *nextnode = &t[pos++];
      nextnode->c = s[i];
      init(nextnode);
      current->next[temp] = nextnode;
    }
    current = current->next[temp]; 
  }
  current->flag_own = true;
  return 0;
}

int set_up_trie_graph() {
  queue<Trie *> q;

  Trie *start = root;
  Trie *temp;
  q.push(root);
  root->hou = root;
  while(!q.empty()) {
    temp = q.front(); 
    q.pop();
    for(int i = 0;i < 26;i++) {
      if(temp->next[i] != NULL) {
	// COMPUTE
	if(temp == root) {
	  temp->next[i]->hou = temp;
	} else {
	  //1)hou is a ac,so 
	  Trie *hou;
	  hou = temp->hou;
	  if(hou->next[i] != NULL) {
	    temp->next[i]->hou = hou->next[i];
	  } else {
	    //if we don't find the hou node
	    while(hou != root) {
	      hou = hou->hou;
	      if(hou->next[i] != NULL) {
		temp->next[i]->hou = hou->next[i];
		break;
	      }
	    }
	    if(hou == root && hou->next[i] == NULL)
	      temp->next[i]->hou = root;
	  }
	  //2) mark the hou node
	  if(temp->next[i]->hou->flag_own == true)
	    temp->next[i]->flag_hou = true;
	}
	//PUSH
	q.push(temp->next[i]);
      }
    }
  }
  return 0;
}

string find(string s) {
  int len = s.length();
  int temp;
  Trie *start = root;

  for(int i = 0;i < len;) {
    temp = s[i] - 'a';
    if(start->next[temp] != NULL) {
      if(start->next[temp]->flag_own == true || start->next[temp]->flag_hou == true) {
	return "YES";
      } else {
        start = start->next[temp];
        i++;
      }
    } else if(start == root) {
      i++;
    } else {
      start = start->hou;
    }
  }
  return "NO";
}


int main() {
  string tmp;
  int n,m;
  string query;

  root = &t[0];
  init(root);
  pos = 1;
  cin>>n;
  for(int i = 0;i < n;i++) {
    cin>>tmp;
    insert(tmp);
  }
  set_up_trie_graph();
  cin>>query;
  cout << find(query) <<endl;

  return 0;
}
