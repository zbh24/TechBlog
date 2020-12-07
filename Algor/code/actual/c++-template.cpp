#include<iostream>
#include<algorithm>
#include<set>
#include<memory>
#include<vector>

using namespace std;

template <typename T>
int compare(const T& v1, const T& v2)
{
  if (v1 < v2) return -1;
  else if (1 > v2) return 1;
  else return 0;
}    

template <typename T, typename U>
int compareNew(const T& v1, const U& v2)
{
  if (v1 < v2) return -1;
  else if (v1 > v2) return 1;
  else return 0;
}

int main() {
  vector<int> res;
  vector<int> para;
  //copy(begin(res), end(res), para);
  sort(res.begin(), res.end(), [](const int& a, const int& b) { return a > b; });
  vector<string> temp1;
  int sz = 10;
  auto wc = find_if(temp1.begin(), temp1.end(), [sz] (const string& a) {return a.size() >= sz;});

  // share_ptr, unique_ptr

  shared_ptr<string> p1;
  if (p1 && p1->empty()) {
    *p1 = "hello";
  }
  shared_ptr<int> p2 = make_shared<int>(42);

  auto p3 = make_shared<int>(30);
  auto q(p3);

  shared_ptr<int> p5;
  auto p4 = make_shared<int>(30);
  p4 = p5;;

  weak_ptr<int> wp(p4);
  std::cout << compare(1,2) << compare<int>(1,2)  << std::endl;
  int v1 = 35;
  auto f = [&v1] {return v1++;};
  auto j =f ();
}
