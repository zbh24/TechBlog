class Solution {
public:
  int findFather(vector<int>& parent, int i) {
    if (parent[i] != i) {
      parent[i] = findFather(parent, parent[i]);
    }
    return parent[i];  
  }
    int makeConnected(int n, vector<vector<int>>& connections) {
      vector<int> parent(n,0);
      for (int i = 0; i < n; i++) {
        parent[i] = i;
      }
      if (connections.size() < (n - 1)) {
        return -1;
      }
      for (auto& item : connections) {
        int first = findFather(parent, item[0]); 
	int second = findFather(parent, item[1]);
	if (first != second) {
          parent[first] = second; 
	}
      }
      for (int i = 0; i < n; i++) {
        findFather(parent, i);
      }
      int res = 0;
      for (int i = 0; i < n; i++) {
        if (parent[i] == i) {
          res++;
	}
      }
      return res - 1;
    }
};
