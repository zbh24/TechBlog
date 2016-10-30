#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <map>

using namespace std;


int find_value(vector<int> &price,int m,vector<int> &repeat) {
  int res = 0;
  int count = 0;
  for (int i = 0; i < m;i++) {
    if (count < repeat.size()) {
      for(int k = 0 ;k < repeat[count];k++)
	res += price[i];
      m = m - repeat[count] + 1;
      count++;
    } else {
      res += price[i];
    }
  }
  return res;
}


int main() {
  int n,m;
  vector<int> input;
  string s;
  int temp;
  int min_v,max_v;
  min_v = max_v = 0;
  map<string,int> list;
  map<string,int>::iterator it;
  vector<int> repeat;

  while (cin >> n >> m) {
    input.clear();
    list.clear();
    repeat.clear();
    for(int i = 0;i < n;i++) {
      cin >> temp;
      input.push_back(temp);
    }

    for(int i = 0; i < m;i++) {
      cin >> s;
      it = list.find(s);
      if (it == list.end()) {
	list.insert(pair<string,int>(s,1));
      } else {
	int count = it->second + 1;
	list.erase(it);
	list.insert(pair<string,int>(s,count));
      }
    }
    for(it = list.begin(); it != list.end();it++) {
      if (it->second != 1)
	repeat.push_back(it->second);
    }
    sort(input.begin(),input.end());
    sort(repeat.begin(),repeat.end());
    reverse(repeat.begin(),repeat.end());

    min_v = find_value(input,m,repeat);
   
    reverse(input.begin(),input.end());
    max_v = find_value(input,m,repeat);
    cout << min_v << " " << max_v << endl;
  }
}
