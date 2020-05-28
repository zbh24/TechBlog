class Solution {
public:
    int shortestBridge(vector<vector<int>>& A) {
      bool found = false;
      queue<std::pair<int, int> > q;
      for (int i = 0; i < A.size() && !found; i++) {
        for (int j = 0; j < A[0].size() && !found; j++) {
          if (A[i][j] == 1) {
            dfs(i, j, A, q);
	    found = true;
          }
        }
      }
      int steps = 0;
      while (!q.empty()) {
        vector<int> dirs = {-1, 0, 1, 0, -1};
	int size = q.size();
	while (size--) {
	  int first = q.front().first;
	  int second = q.front().second;
          q.pop();
          bool flag = false;
	  for (int i = 0 ; i < 4;i++) {
	    int row = dirs[i] + first;
	    int col = dirs[i + 1] + second;
	    if (row < 0 || row >= A.size() || col < 0 || col >= A[0].size() || A[row][col] == 2)
	      continue;
	    if (A[row][col] == 1) {
	      return steps;
	    }
	    if (A[row][col] == 0) {
              A[row][col] = 2;
	      flag = true;
              q.push(std::pair<int, int>(row, col));
	    }
	  }
	}
        steps++;
      }
      return -1;
    }

  void dfs(int i, int j, vector<vector<int>>& A, queue<std::pair<int, int> >& q) {
    if (i < 0 || j < 0 || i >= A.size() || j >= A[0].size() || A[i][j] != 1) {
      return;
    }
    A[i][j] = 2;
    q.push(std::pair<int, int>(i, j));
    dfs(i - 1, j, A, q);
    dfs(i + 1, j, A, q);
    dfs(i, j - 1, A, q);
    dfs(i, j + 1, A, q);
  }
};
