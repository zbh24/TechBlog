#include <iostream>
#include <vector>
#include <string>
#include <algorithm>

using namespace std;


bool compare(int a,int b)
{
      return a<b;   //升序排列，如果改为return a>b，则为降序

}

int main ()
{
     int a[20]={2,4,1,23,5,76,0,43,24,65};
     int i;
     for(i=0;i<20;i++)
       cout<<a[i]<<" ";
     cout << endl;

     sort(a,a+20,compare);
     for(i=0;i<20;i++)
       cout<<a[i]<<" ";

     cout <<endl;
     return 0;
}
