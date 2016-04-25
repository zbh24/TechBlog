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


// struct arcnode {
//   int to;
//   int dis;
//   struct arcnode *next;
// };

// struct {
//   struct arcnode *first;
// } adjlist[MAX];

// #define maxvalue 100000
//int a[100010][100010] = new int[100010][100010] ;
#define maxedge 1000100
#define maxnode 100100
#define INF 0x7fffffff

struct edge {
  int to;
  int dis;
  int next;
};

struct edge edge[maxedge];
int head[maxnode];
int num;
int dis[maxnode];

void  addedge(int i,int j,int temp) {
  edge[num].to = j;
  edge[num].dis = temp;
  edge[num].next = head[i];
  head[i] = num++;
}

void init() {
  num = 0;
  for(int i = 0;i < maxnode;i++) {
    dis[i] = -1;
    head[i] = -1;
  }
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
    for(int i = head[start];i != -1;i = edge[i].next) {
      int to = edge[i].to;
	if(dis[to] == -1 || edge[i].dis + dis[start] < dis[to]) {
	  dis[to] = edge[i].dis + dis[start];
	  if(vis[to] == false) {
	    q.push(to);
	    vis[to] = true;
	  }
	} 
    }
  }
  return dis[dst]; 
}


// int spfa(int n,int src,int dst) {
//   queue<int> q;
//   bool vis[n] ;

//   for(int i = 1;i <=n;i++)
//     vis[i] = false;
  
//   dis[src] = 0;
//   q.push(src);
//   vis[src] = true;
//   while(!q.empty()) {
//     int start,cur_dis;
//     start = q.front();
//     q.pop();
//     vis[start] = false;
//     cur_dis = dis[start];
//     for(int i = 1;i <= n;i++) {
//       if(a[start][i] != -1 ) {
// 	if(dis[i] == -1 || a[start][i] + dis[start] < dis[i]) {
// 	  dis[i] = a[start][i] + dis[start];
// 	  if(vis[i] == false) {
// 	    q.push(i);
// 	    vis[i] = true;
// 	  }
// 	}
//       } 
//     }
//   }
//   return dis[dst]; 
// }



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




// 5 4 5 4

// 5 1 200
// 1 4 300
// 3 4 150
// 5 3 400
// // 500

// 5 5 5 4
// 5 1 200
// 1 2 300
// 3 4 150
// 5 3 400
// 2 4 30
// 530
