class Solution {
public:
    int slidingPuzzle(vector<vector<int>>& board) {
      string target = "123450";
      string start;
      for (int i = 0; i < board.size();i++) {
        for (int j = 0;j < board[0].size(); j++) {
	  start += to_string(board[i][j]);
	}
      }

      queue<string> q;
      q.push(start);
      vector<vector<int>> dirs = {{ 1, 3 }, { 0, 2, 4 },
                                      { 1, 5 }, { 0, 4 },
				      { 1, 3, 5 }, { 2, 4 }};
      int res = 0;
      set<string> visited;
      if (start.compare(target) == 0) {
        return 0;
      }
      while (!q.empty()) {
	int size = q.size();
	while (size--) {
          string s = q.front();
	  q.pop();
          visited.insert(s);
          int stringIndex = s.find("0");
          vector<int> temp = dirs[stringIndex];
	  for (auto c : temp) {
	    string newS = s;
	    swap(newS[stringIndex], newS[c]);
	    if (newS.compare(target)  == 0) {
              return res + 1;
	    } else if (!visited.count(newS)) {
	      q.push(newS);
            }
	  }
	}
        res++;
      }
      return -1;
    }
};
