#include <utility>
#include <queue>
#include <vector>
#include <cstdio>
using namespace std;
vector<vector<int>> dir = {{1, 0}, {-1, 0}, {0, 1}, {0,- 1}};
int row ,col ;
int checklocal(vector<vector<int>> table, int x, int y)
{
    if (table[x + 1][y] == 2 && table[x - 1][y] == 2 && table[x][y + 1] == 2 && table[x][y - 1] == 2){
        return 0;
    } 
    return 1;
}
int BfSearch(vector<vector<int>> &table, queue<pair<int, int>> &Record,int x, int y)
{
    pair<int,int> point;
    vector<vector<int>> visited(row + 2, vector<int>(col + 2, 0xffff));
    visited[x][y] = 0;
    int step = 0;
    int a = 0,b = 0;
    int res = 0xffff;
    while(!Record.empty()) {
        point = Record.front();
	Record.pop();
        a = point.first;
        b = point.second;
        for (int i = 0; i < dir.size(); i++) {
            int k = a + dir[i][0];
            int t = b + dir[i][1];
            if(table[k][t] == 2) {
                continue;
            }
            if (visited[k][t] > visited[a][b] + 1) {
                visited[k][t] = visited[a][b] + 1;
                if (table[k][t] == 1){ //find a shop
                    res = min(visited[k][t], res); //record the minipath
                }
                point.first = k;
                point.second = t;  
                Record.push(point);
            }  
        }
    }
    return res;
}
int main(){
    cin >> row >> col;
    vector<vector<int>> Table(row + 2, vector<int>(col + 2, 0));
    queue<pair<int, int>> Record;
    for (int i = 0; i < row + 2; ++i) {
        for (int j = 0; j < col + 2; ++j) {
             if (i == 0 || j == 0 || i == row + 1 || j == col + 1) {
                   Table[i][j] = 2;//wall
             }
        }
    }
    int k;
    cin >> k;
    for (int i = 0; i < k; ++i) {
        int a, b;
        cin >> a >> b;
        a = a + 1;
        b = b + 1;
        Table[a][b] = 1; //shop
    }
    cin >> k;
    for (int i = 0; i < k; ++i) {
        int a, b;
        cin >> a >> b;
        a = a + 1;
        b = b + 1;
        Table[a][b] = 2; //wall
    }
    cin >> k;
    int min = 0;
    for (int i = 0; i < k; ++i) {
        int a, b;
        cin >> a >> b;
        a = a + 1;
        b = b + 1;
        Record.push(make_pair(a,b));
        if (checklocal(Table, a, b)) {
            min += BfSearch(Table, Record, a, b);
        }
    }
    cout << min * 2 << endl;
    return 0;
}
