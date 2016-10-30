#include <iostream>
#include <string>
#include <vector>
#include <sstream>
#include <algorithm>

using namespace std;

int main() {
  int i = 100;
  stringstream ss;
  string temp;
  ss << i;
  temp = ss.str();
  cout << temp <<endl;
  
  return 0;
}
