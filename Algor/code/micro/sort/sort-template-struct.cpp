#include <iostream>
#include <vector>
#include <string>
#include <algorithm>

using namespace std;

struct node {
  int x;
  int y;
};
typedef struct node node;
node dij[100];

bool compare(node a,node b)
{
  return a.y <=  b.y;
}

int main ()
{
  int i;
  for (i = 0; i < 10;i++) {
    dij[i].x = i;
    dij[i].y = 100 + 'a'- i;
  }
  sort(dij,dij+10,compare);

  for(int i = 0;i < 10;i++)
    cout << dij[i].x << ":" << dij[i].y << endl;
  return 0;
}
