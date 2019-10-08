#include<iostream>
#include<vector>
#include<algorithm>

using namespace std;

using persion = struct persion {
  int x;
  persion(int p) {
    x = p;
  }
  bool operator < (const persion &p) {
    return x < p.x;
  }
};

struct Cmp {
  bool operator () (persion p1, persion p2)  {
    return p1.x < p2.x;
  }
};

static bool cmp (persion p1, persion p2) {
  return p1.x < p2.x;
}

int main() {
  persion p1(3);
  persion p2(4);
  vector<persion> vec;
  vec.push_back(p1);
  vec.push_back(p2);
  sort(vec.begin(), vec.end(), [](persion &p1, persion &p2) { return p1.x < p2.x;});
  sort(vec.begin(), vec.end(), Cmp());
  sort(vec.begin(), vec.end(), cmp);
  return 0;
}
