#include <iostream>
#include <stdio.h>
#include <vector>

using namespace std;

int N,M;
string str;
vector<string> maze(100);
bool res = false;
bool flag[100][100] = {false}; 

void dfs(int loc_i ,int loc_j, int pos) {
  if (pos == str.length()) {
    res = true;
    return;
  }

  if (maze[loc_i][loc_j] == str[pos]) {
    flag[loc_i][loc_j] = true;
    if (pos == str.length() - 1) {
      res = true;
      return;
    }

    if (loc_i + 1 < N && flag[loc_i + 1][loc_j] == false) 
      dfs(loc_i+1, loc_j, pos + 1);
    if (res == true)
      return;

    if (loc_j + 1 < M && flag[loc_i][loc_j + 1] == false) 
      dfs(loc_i, loc_j + 1,pos + 1);
    if (res == true)
      return;

    if (loc_i - 1 >= 0 && flag[loc_i - 1][loc_j] == false) 
      dfs(loc_i-1, loc_j, pos + 1);
    if (res == true)
      return;

    if (loc_j - 1 >= 0 && flag[loc_i][loc_j - 1] == false) 
      dfs(loc_i, loc_j - 1,pos + 1);
    if (res == true)
      return;

    flag[loc_i][loc_j] = false;
  }
}

int main() {
  cin >> N >> M;
  cin >> str;

  for (int i = 0;i < N;i++)
    cin >> maze[i];

  for (int i = 0;i < N;i++)
    for(int j = 0; j < M;j++)
      dfs(i, j , 0);

  if (res) {
    cout << "YES" << endl;
  } else {
    cout << "NO" << endl;
  }
  return 0;
}
