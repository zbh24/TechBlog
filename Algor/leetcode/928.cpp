class Solution {
public:
    int minMalwareSpread(vector<vector<int>>& graph, vector<int>& initial) {
      int N = graph[0].size();
      vector<int> good(N, 1);
      for (int i = 0; i < initial.size(); i++) {
        good[initial[i]] = 0;
      }
      map<int ,set<int> > infected;
      for (int i = 0; i < initial.size(); i++) {
	vector<int> visited(N, 0);
	dfs(graph, good, initial[i], initial[i], vistied, infected); 
      }

      vector<int> res(N, 0);
      for (int i = 0; i < N; i++) {
        if (good[i] == 1) {
          if (infected[i].size() == 1) {
            res[infected[i].get(0)]++;
	  }
	}
      }
      sort(initial.begin(), initial.end());
      int loc = 0;
      int max = -1;
      for (int i = 0; i < initial.size(); i++) {
        if (res[i] > max) {
          max = res[i];
	  loc = i;
	}
      }
      return loc;
    }

    void dfs(vector<vector<int>>& graph, vector<int>& good, int first, int loc, vector<int>& visited, map<int ,set<int> >& infected) {
      for (int i = 0; i < graph[0].size(); i++) {
        if (graph[loc][i] == 1 && good[i] == 1 && visited[i] == 0) {
          visited[i] = 1;
	  infected[i].insert(first);
	  dfs(graph, good, first, i, visited, infected);
	}
      }
   }
};
