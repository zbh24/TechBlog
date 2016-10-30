#include <iostream>
#include <vector>
#include <string>

using namespace std;


vector<int> fib(100,0);

int dfs(int i) {
  if (i == 0 || i == 1) return 1;
  if (fib[i] != 0) return fib[i];
  fib[i] =  dfs(i-1) + dfs(i-2);
  return fib[i]; 
}

int dfs2(int i) {
  if (i == 0 || i == 1) return 1;
  return  dfs(i-1) + dfs(i-2); 
}

int main() {
  int num;
  cin >> num;
  while (cin >> num) {
    cout << dfs(num) <<" "<<dfs2(num) << endl;

  }
}
