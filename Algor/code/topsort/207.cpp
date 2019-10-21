#include<iostream>
#include<vector>
#include<map>
#include<set>

using namespace std;

  bool haveNoVisited(bool visited[], int len) {
    for (int i = 0;i < len;i++)
      if (visited[i] == false)
	return true;

    return false;
  }

bool findNode(int degree[], bool visited[], int len, int &node) {
    for (int i = 0; i < len; i++) {
      if (degree[i] == 0 && visited[i] == false) {
	node = i;
	return true;
      }
    }
    return false;
  }

    bool canFinish(int numCourses, vector<vector<int> >& prerequisites) {
      bool visited[1001] = {false};    
      std::map<int, std::set<int> > edges;
      int degree[1001] = {0};
      int size = prerequisites.size();
      for (int i = 0; i < size; i++) {
        vector<int> &temp = prerequisites[i];
	edges[temp[0]].insert(temp[1]);
        degree[temp[1]]++;
      }
      bool flag = true;
      while (haveNoVisited(visited, numCourses)) {
	int v;
        if (findNode(degree, visited, numCourses, v)) {
	  visited[v] = true;
	  for (auto node : edges[v]) {
            degree[node]--;
	  }
	} else {
          flag = false;
	  break;
	}
      }
      return flag;
    }

int main() {
  vector<int> first;
  vector<vector<int> > res;
  first.push_back(0);
  first.push_back(1);
  res.push_back(first);
  canFinish(2, res);
  return 1;
}
