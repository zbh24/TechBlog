#include <iostream>

#include <vector>

#include <map>
#include <string>
#include <unordered_map>
#include <mutimap>


using namespace std;

int main() {
  //map<string,int> num;
  //map<string,int>::iterator it;
  unordered_map<string,int> num;
  unordered_map<string,int>::iterator it;
  string s;
  while (cin >> s) {
    num[s]++;
  }
  for(it = num.begin(); it != num.end();it++)
    cout <<it->first<< "," <<it->second << " ";
  cout <<endl;

}
