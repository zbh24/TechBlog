#include <iostream>
#include <vector>
#include <queue>
#include <string>

using namespace std;

#define maxnode 1000100
#define maxedge 1000100

struct edge {
  int to;
  int dis;
  int next;
};

typedef struct edge Edge;


int head[maxnode];
Edge e[maxedge];
int count = 0;
int dis[maxnode];
//int dis[maxnode] = {-1};


// just for the test
// int test1[100];
// int test2[100] = {0};
// bool t[100] = {false};
// bool s[100] =  {true,};

void init() {
  count = 0;

  for(int i = 0;i < maxnode;i++) {
    head[i] = -1;
    dis[i] = -1;
  }

  for(int i = 0;i < maxedge;i++) {
    e[i].to = -1;
    e[i].dis = -1;
    e[i].next = -1;
  }
}

void addedge(int from,int to,int dis) {
  e[count].dis = dis;
  e[count].to = to;
  // head insert
  e[count].next = head[from];
  head[from] = count;
  count++;
}

void trans(int node) {
  int start;
  for(start = head[node]; start != -1;start = e[start].next)
    cout <<   node << " to " << e[start].to <<": "<< e[start].dis << endl;
  return ;
}


int spfa(int n,int src,int dst) {
  queue<int> q;
  bool vis[n] ;

  for(int i = 1;i <=n;i++)
    vis[i] = false;
  
  dis[src] = 0;
  q.push(src);
  vis[src] = true;
  while(!q.empty()) {
    int start,cur_dis;
    start = q.front();
    q.pop();
    vis[start] = false;
    cur_dis = dis[start];
    for(int i = head[start];i != -1;i = e[i].next) {
      int to = e[i].to;
	if(dis[to] == -1 || e[i].dis + dis[start] < dis[to]) {
	  dis[to] = e[i].dis + dis[start];
	  if(vis[to] == false) {
	    q.push(to);
	    vis[to] = true;
	  }
	} 
    }
  }
  return dis[dst]; 
}

int main() {
  int N,M,S,T;
  int i;
  int fst,snd,temp;

  cin>>N>>M>>S>>T;
  init();
  for(i = 0;i < M;i++) {
    cin>>fst>>snd>>temp;
    addedge(fst,snd,temp);
    addedge(snd,fst,temp);
  }
  cout<<spfa(N,S,T)<<endl;
}
