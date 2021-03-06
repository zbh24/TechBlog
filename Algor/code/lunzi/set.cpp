#include <iostream>
#include <set>
#include <map>
using namespace std;


int main()
{
    set<int> st1;                //创建一个int类型的set
    set<int>::iterator it1;        //创建一个他对应的迭代器

    //empty是判断他是否为空，而且如果要判断空，最好用这个来判断
    //如果为空返回true
    if (st1.empty())            //判断空,如果是空，则输出empty
    {
        cout << "empty\n";
    }

    //查找数据，find。返回值是找到的情况的迭代器，如果没有找到，
    //迭代器只想end，如果找到，为找到的数据，所以这里一定要先
    //判断一下是否找到数据了。
    it1 = st1.find(40);            //查找数据
    //it1 = find(st1.begin(),st1.end(),40);
    if (it1 != st1.end())        //如果找到就输出数据
    {
        cout <<  *it1 << endl;
    }
    
    //插入数据。
    st1.insert(10);                //插入数据
    st1.insert(30);
    st1.insert(20);
    st1.insert(40);                

    //遍历数据，用迭代器遍历数据
    for (it1 = st1.begin(); it1 != st1.end(); ++it1)    
    {
        cout << *it1 << endl;
    }
    
    //因为开始没有40这个元素，所以找不到，现在插入了，再
    //寻找一下。呵呵，找到了。
    it1 = st1.find(40);            //查找数据
    if (it1 != st1.end())        //如果找到就输出数据
    {
        cout <<  *it1 << endl;
    }

    //删除数据这里返回的是删除的个数。在这里当然是1咯
    size_t kk = st1.erase(40);
    cout << kk << endl;

    //清除全部数据。
    st1.clear();

    //set<int,int> test_set;
    //test_set.insert(1,2);
    map<int,string> ss;
    return 0;
}
