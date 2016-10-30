#include <iostream>

using namespace std;

int main() {
  int begin,end,price;
  do {
    cin.get();//[
    cin>>begin;
    
    cin.get();//,
    cin>>end;

    cin.get();//,
    cin>>price;

    cin.get();//]
    cout << begin << " " << end <<":"<< price << endl;
  
  } while (cin.get() == ',');
  
  return 0;
}

