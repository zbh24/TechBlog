class Solution {
public:
    struct T {
      int color;
      int colorSize;
      int loc;
      T(int a, int b, int c) : color(a), colorSize(b), loc(c) {}
      bool operator < (const T &t) {
        if (colorSize > t.colorSize) {
          return true;
        } else if (colorSize == t.colorSize && loc < t.loc) {
          return true;
        } else {
          return false;
        }
      }
      bool operator == (const T &t) {
        return t.color == color;
      }
    };

    void dfs(vector<vector<int>>& graph, vector<int>& visited, int loc, int color, map<int, int>& colorNum) {
      for (int i = 0; i < graph[0].size(); i++) {
        if (graph[loc][i] == 1 && visited[i] == 0) {
          visited[i] = color;
          colorNum[color]++;
          dfs(graph, visited, i, color, colorNum);
        }
      }
    }

    int minMalwareSpread(vector<vector<int>>& graph, vector<int>& initial) {
      int N = graph[0].size();
      int color = 1;
      vector<int> visited(N, 0);
      map<int, int> colorNum;
      for (int i = 0; i < N; i++) {
        if (visited[i] == 0) {
          dfs(graph, visited, i, color, colorNum);
          color++;
        }
      }

      vector<T> res;
      for (int i  = 0; i < initial.size(); i++) {
        int tempColor = visited[initial[i]];
        T temp(tempColor, colorNum[tempColor], initial[i]);
        if (find(res.begin(), res.end(), temp) != res.end()) {
          auto it = find(res.begin(), res.end(), temp);
          it->colorSize = 0;
          it->loc = it->loc > initial[i] ? initial[i] : it->loc;

        } else {
          res.emplace_back(temp);
        }
      }
      sort(res.begin(), res.end());
      return res[0].loc;
    }
};
