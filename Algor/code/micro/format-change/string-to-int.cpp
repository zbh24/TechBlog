#include <iostream>
#include <string>
#include <vector>
#include <sstream>
#include <algorithm>

using namespace std;

int main() {
  string temp = "100";
  int i = 0;
  
  istringstream ss(temp);
  ss >> i;
  cout << i <<endl;
  
  return 0;
}
