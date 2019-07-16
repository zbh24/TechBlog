#include "iostream"
#include <string>
#include <map>

using namespace std;

typedef struct zbh {
  int index;
  zbh(int t) {
    index = t;
  }
  friend bool operator < (const zbh z1, const zbh z2) {
    return z1.index < z2.index;
  }
} zbh;

int main() {
  std::string s = "hello";
  std::map<string, int> testmap1;
  testmap1.insert(pair<string,int>(s,100));
  for (auto &item : testmap1) {
    cout << "test: " << item.first << endl;
  }
  zbh z(12);
  std::map<zbh,string> testmap2;
  testmap2.insert(pair<zbh,string>(z,s));
  for (auto &item : testmap2) {
    cout << "test: " << endl;
  }

  std::map<zbh*, string> testmap3;
  testmap3.insert(pair<zbh*, string>(&z,s));
  for (auto &item : testmap3) {
    cout << "test: " << endl;
  }

  zbh *asdf = new zbh(100);
  std::map<zbh*, string> testmap4;
  testmap4.insert(pair<zbh*, string>(&z,s));
  for (auto &item : testmap4) {
    cout << "test: " << endl;
  }
}
