class Solution {
public:
struct T {
  int color;
  int value;
  int loc;
  T (int a, int b,int c) : color(a), value(b), loc(c) {}
  const bool operator < (const T& t) const {
    return (value > t.value) || (value == t.value && loc < t.loc);
  }
  const bool operator == (const T& t) const {
    return color ==  t.color;
  }
};


int findFather(vector<int>& father, int i) {
  if (father[i] == i) {
    return i;
  } else  {
    father[i] = findFather(father, father[i]);
    return father[i];
  }
}



    void unionT(vector<int>& father,int i, int j) {
  int temp1 = findFather(father, i);
  int temp2 = findFather(father, j);
  if (temp1 == temp2) {
    return;
  } else if (temp1 < temp2) {
    father[temp1] = temp2;
 
  } else {
    father[temp2] = temp1;
  
  }
}


    int minMalwareSpread(vector<vector<int>>& graph, vector<int>& initial) {
          int N = graph[0].size();
  vector<int> father(N, 0);
         
  for (int i = 0; i < N; i++) {
    father[i] = i;
  }

  for (int i = 0; i < N; i++) {
    for (int j = 0; j < N; j++) {
      if (graph[i][j] == 1) {
        unionT(father,i ,j);
      }
    }
  }



  map<int, set<int> > colorNum;
  for (int i = 0; i < N; i++) {
    colorNum[findFather(father,i)].insert(i);
  }
  sort(initial.begin(), initial.end());
  vector<T> res;
    for (auto& item : initial) {
    int tempV = item;
    int size = colorNum[father[item]].size();
    int color = father[item];
    T temp(color, size, item);
    if (find(res.begin(), res.end(), temp) != res.end()) {
      auto it = find(res.begin(), res.end(), temp);
      it->value = 0;
    } else {
      res.push_back(temp);
    }
  }
  sort(res.begin(), res.end());
  return res[0].loc;

        
    }
};
