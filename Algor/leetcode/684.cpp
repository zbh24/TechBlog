class Solution {
public:


    bool dfs(map<int ,set <int>>& graph, int start, int target, vector<int>& visited) {
      if (visited[start] == 0) {
        if (start == target) {
	  return true;
	}
        visited[start] = 1;
        for (auto& item : graph[start]) {
          if (dfs(graph, item, target, visited)) {
            return true;
	  }
        }
      }
      return false;
    }

    vector<int> findRedundantConnection(vector<vector<int>>& edges) {
      int N = edges.size() + 1;
      map<int, set<int> > graph;
      vector<int> res;
      for (auto& item : edges) {
        int start = item[0];
	int end = item[1];
	vector<int> visited(N ,0);
        if (graph.count(start) == 1 && graph.count(end) == 1 && dfs(graph, start, end, visited)) {
	  res.push_back(start);
	  res.push_back(end);
          return res;
        } else {
          graph[start].insert(end);
	  graph[end].insert(start);
        }
      }
      return res;
    }
};
