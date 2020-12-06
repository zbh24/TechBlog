#include<iostream>
#include<stack>
#include<vector>
#include<set>
#include<map>
#include<unordered_map>
#include<algorithm>

using namespace std;

struct T {
  int row;
  int col;
  T(int a, int b) : row(a), col(b) {}
  const bool operator < (const T& t) const {
    return (row < t.row) || (row == t.row && col < t.col);
  }

  const bool operator == (const T& t) const {
    return row == t.row && col == t.col;
  }
};

void dfs(const vector<vector<int>>& grid, int row, int col, int fakeRow, int fakeCol, vector<vector<int>> &visited, map<T, set<int>>& infect, int loc) {
  if (row < 0 || row >= grid.size() || col < 0 || col >= grid[0].size()) {
    return;
  }
  if (visited[row][col] == 1) {
    return;
  }
  if (grid[row][col] != 1) {
    return;
  }
  infect[T(row,col)].insert(loc);
  if (row == fakeRow && col == fakeCol) {
    return;
  }
  visited[row][col] = 1;
  dfs(grid, row + 1, col, fakeRow, fakeCol, visited,  infect, loc);
  dfs(grid, row - 1, col, fakeRow, fakeCol, visited, infect, loc);
  dfs(grid, row, col + 1, fakeRow, fakeCol, visited, infect, loc);
  dfs(grid, row, col - 1, fakeRow, fakeCol, visited, infect, loc);
}

int ConnectivityTest(const vector<vector<int>>& grid, int row, int col)
{
  int rowN = grid.size();
  int colN = grid[0].size();
  vector<vector<int>> visited(rowN, vector<int>(colN, 0));
  map<T ,set<int> > infect;
  dfs(grid, 0, 0, row, col, visited, infect, 0);
  vector<vector<int>> visited1(rowN, vector<int>(colN, 0));
  dfs(grid, row, col, 0, 0, visited1, infect, 1);

  int res = 0;
  if (!infect[T(row,col)].count(0)) {
    return 0;
  }
  for (auto& item : infect) {
    if (item.second.size() == 1 && *item.second.begin() == 1) {
      res++;
    }
  }
  return res;
}

int main() {
  vector<vector<int> > mutexPairs = {{1,1,0,0,0},{0,0,0,0,0},{1,1,1,1,1}};
  return ConnectivityTest(mutexPairs, 0, 1);
}
