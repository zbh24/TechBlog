#include<iostream>
#include<set>
#include<map>
#include<vector>

using namespace std;

struct T {
  int value;
  int loc;
  T(int a, int b) : value(a), loc(b) {}
  const bool operator < (const T& t) const {
    return (value < t.value) || (value == t.value && loc < t.loc);
  }
  const bool operator == (const T& t) const {
    return (value == t.value && loc == t.loc);
  }
};

int main() {
  vector<T> res;
  map<T, set<T>> res1; 
  res1[T(3,4)].insert(T(5,6)); 
  map<T, int> res2;
  res2[T(4,5)]++; 
}
