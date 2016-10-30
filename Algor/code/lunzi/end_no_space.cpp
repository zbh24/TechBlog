#include <iostream>
#include <vector>

using namespace std;


int main() {
  vector<int> num(20,0);
  for(int i = 0;i < 19;i++) {
    cout << num[i];
    if (i < 18) cout << " ";
  }
  cout << endl;
  return 0;
}
