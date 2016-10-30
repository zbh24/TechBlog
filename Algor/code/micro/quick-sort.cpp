#include <iostream>
#include <string>
#include <vector>
#include <algorithm>
#include <map>

using namespace std;


int part(int A[],int low,int high) {
  int key = A[low];

  while(low < high) {
    while(low < high && A[high] >= key) {
      high--;
    }
    swap(A[low],A[high]);
    
    while(low < high && A[low] <= key) {
      low++;
    }
    swap(A[low],A[high]);
  }
  return low;
}

// because the shuzhou assian doesn;t need,so the change is can be this
// The first one is shuzhou

int part1(int A[],int low,int high) {
  int key = A[low];

  while(low < high) {
    while(low < high && A[high] >= key) {
      high--;
    }
    A[low] = A[high];
    while(low < high && A[low] <= key) {
      low++;
    }
    A[high] = A[low];
  }

  A[low] = key;
  return low;
}

void qsort(int A[],int low,int high) {
  int loc;  
  if(low < high) {
      loc = part(A,low,high);
      qsort(A,low,loc - 1);
      qsort(A,loc + 1,high);
  }
}


// void sort-mp-second-int() {
//   map<string,int> mp;  
//   map<int,string> test;
//   // 1.step :insert the mp into the test
//   // 2.step :cpoy the test the first element into the maxtix
//   // 3.step :sort the maxtrix
//   // 4.step :cout the elment of the test by the maxtrix order
// }

// void sort-mp-first-string() {
//   // 1.step: copy the string into the set,it will be order
//   // 2.
  

// }



int main() {
  map<string,int> mp;  
  string s;
  int m;
  cin >> m;
  int count = 1;
  for(int i = 0;i < m;i++) {
    cin >> s;
    mp.insert(pair<string,int>(s,count++));
  }
  map<string,int>::iterator it;
  for(it = mp.begin();it != mp.end();it++)
    cout << it->first << " : " << it->second <<endl;

  return 0;

}


