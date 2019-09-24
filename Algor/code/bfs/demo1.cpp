#include <iostream>
#include <vector>
#include <queue>
using namespace std;
struct Point
{
public:
    Point(int inX = 0, int inY = 0) : x{inX}, y{inY} {}
    int x;
    int y;
};
// 1 is target, 2 is dead point
int shortestCount(vector<vector<char>>& a, queue<Point>& q, int n, int m)
{
    int count = 0;
    int sum = 0;
    int visited[n][m] = {0};
    bool reachTarget = false;
    for (int i = 0; i < n; i++) {
        for (int j = 0; j < m; j++) {
            visited[i][j] = 0;
        }
    }
    while (!q.empty()) {        
        for (int i = q.size(); i > 0; i--) {
            Point pt = q.front();
            q.pop();
            if (visited[pt.x][pt.y] == 1) {
                continue;
            }
            visited[pt.x][pt.y] = 1;
            if (a[pt.x][pt.y] == 1) {
                sum += count;
                reachTarget = true;                
            }
            if (pt.x - 1 >= 0 && visited[pt.x-1][pt.y] == 0 && a[pt.x-1][pt.y] != 2) {
                q.push(Point(pt.x-1, pt.y));
            }
            if (pt.x + 1 < n && visited[pt.x+1][pt.y] == 0 && a[pt.x+1][pt.y] != 2) {
                q.push(Point(pt.x+1, pt.y));
            }
            if (pt.y - 1 >= 0 && visited[pt.x][pt.y-1] == 0 && a[pt.x][pt.y-1] != 2) {
                q.push(Point(pt.x, pt.y-1));
            }
            if (pt.y + 1 < m && visited[pt.x][pt.y+1] == 0 && a[pt.x][pt.y+1] != 2) {
                q.push(Point(pt.x, pt.y+1));
            }
        }
        count++;
    }
    return reachTarget ? sum : 0;
}
int main(){
    int n, m;
    cin >> n >> m;
    vector<vector<char>> a(n, vector<char>(m, 0));
    int k;
    cin >> k;
    queue<Point> starts;
    for (int i = 0; i < k; i++) {
        Point pt;
        cin >> pt.x >> pt.y;
        starts.push(pt);
        a[pt.x][pt.y] = 8;
    }
    int z;
    cin >> z;
    for (int i = 0; i < z; i++) {
        int x, y;
        cin >> x >> y;
        a[x][y] = 2;
    }
    int h;
    cin >> h;
    for (int i = 0; i < h; i++) {
        int x, y;
        cin >> x >> y;
        a[x][y] = 1;
    }
    int count = shortestCount(a, starts, n, m);
    std::cout << count*2;
    return 0;
}
