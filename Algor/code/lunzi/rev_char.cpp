#include <iostream>
#include <vector>
#include <string>

using namespace std;

int  rev_char(string& s) {
  int i,j;
  char c;
  i = 0;
  j = s.length() -1;
  while (i < j) {
    c = s[i];
    s[i] = s[j];
    s[j] = c;
    i++;
    j--;
  }
  return 0;
}

int main() {
  string s1 = "hello";
  string s2 = "abcd";
  rev(s1);
  rev(s2);
  cout << s1 << " "<< s2 <<endl;
  return 0;
}
