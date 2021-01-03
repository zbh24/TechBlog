class Solution {
public:

  void dfs(map<int, set<int>>& graph, vector<bool>& visited, int src) {
    visited[src] = true;
    for (auto& item : graph[src]) {
      if (!visited[item]) {
        dfs(graph, visited, item);
      }
    }
  }
    int makeConnected(int n, vector<vector<int>>& connections) {
      if (connections.size() < (n - 1)) {
        return -1;
      }
      vector<bool> visited(n, false); 
      int res = 0;
      map<int ,set<int> > graph;
      for (auto& item : connections) {
	graph[item[0]].insert(item[1]);
	graph[item[1]].insert(item[0]);
      }
      for (int i = 0;i < n;i++) {
        if (visited[i] == false) {
	  res++;
          dfs(graph ,visited, i);
	}
      }
      return res - 1;
    }
};
