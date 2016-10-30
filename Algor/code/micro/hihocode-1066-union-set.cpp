#include <iostream>
#include <vector>
#include <string>
#include <map>

using namespace std;

#define MAX 100010

int father[MAX];
int rank_node[MAX];

void mark_set(int x) {
  father[x] = x;
  rank_node[x] = 0;
}

int find_set(int x) {
  if (x != father[x]) {
    father[x] = find_set(father[x]);
  }
  return father[x];
}

void union_set(int x,int y) {
  int a = find_set(x);
  int b = find_set(y);
  if (a == b)
    return;
  if (rank_node[a] > rank_node[b])
    father[b] = a;
  
  else {
    if (rank_node[a] == rank_node[b])
      rank_node[b]++;
    father[a] = b;
  }
}

int main() {
  int num;
  cin >> num;
  int op;
  string s1,s2;
  int nstart = 0;

  map<string,int> mp;
  map<string,int>::iterator it;
  int fid,sid;

  for(int i = 0;i < num;i++) {
    cin >> op >> s1 >> s2;
    if (op == 0) {
      it = mp.find(s1);
      if(it == mp.end()) {
	fid = nstart;
	mark_set(nstart);
	mp.insert(pair<string,int>(s1,nstart++));
      } else
	fid = it->second;
     
      it = mp.find(s2);
      if(it == mp.end()) {
	sid = nstart;
	mark_set(nstart);
	mp.insert(pair<string,int>(s2,nstart++));
      } else
	sid = it->second;
      union_set(fid,sid);
    }

    if (op == 1) {
      it = mp.find(s1);
      if (it == mp.end()) {
	cout << "no" <<endl;
	continue;
      }
      fid = it->second;
      it = mp.find(s2);
      if (it == mp.end()) {
	cout << "no" <<endl;
	continue;
      }
      sid = it->second;
      if (find_set(fid) == find_set(sid))
	cout << "yes"<<endl;
      else
	cout <<"no"<<endl;
    }
  }
  return 0;
}
