#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>
#include <iostream>
#include <string>
#include <set>
#include <vector>
#include <algorithm>
#include <map>
#include <sstream>
#include <queue>

using namespace std;

#define SIZE 1000010
long long d[SIZE] = {0};
queue<long long> q;

int fun() {


}


int main() {
  int N;
  cin >> N;
  long long temp;
  for(int i = 1;i <= N;i++) {
    cin >> temp;
    q.push(temp);
  }
  return 0;
}
