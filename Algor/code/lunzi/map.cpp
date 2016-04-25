//multimap允许重复的键值插入容器  
//        **********************************************************        
//        * pair只包含一对数值:pair<int,char>                       *  
//        * map是一个集合类型，永远保持排好序的，                   *  
//  pair  * map每一个成员就是一个pair,例如：map<int,char>           *  
//        * map的insert()可以把一个pair对象作为map的参数,例如map<p> *  
//        ***********************************************************  
#pragma warning(disable:4786)  
#include<map>  
#include<iostream>  
using namespace std;  
  
int main(void)  
{  
 multimap<int,char*> m;  
 //multimap的插入只能用insert()不能用数组  
 m.insert(pair<int,char*>(1,"apple"));  
    m.insert(pair<int,char*>(1,"pear"));//apple和pear的价钱完全有可能是一样的  
 m.insert(pair<int,char*>(2,"banana"));  
 //multimap的遍历只能用迭代器方式不能用数组  
 cout<<"***************************************"<<endl;  
 multimap<int,char*>::iterator i,iend;  
 iend=m.end();  
 for(i=m.begin();i!=iend;i++)  
 {  
  cout<<(*i).second<<"的价钱是"  
   <<(*i).first<<"元/斤\n";  
 }  
 cout<<"***************************************"<<endl;  
    //元素的反相遍历  
 multimap<int,char*>::reverse_iterator j,jend;  
 jend=m.rend();  
 for(j=m.rbegin();j!=jend;j++)  
 {  
  cout<<(*j).second<<"的价钱是"  
   <<(*j).first<<"元/斤\n";  
 }  
 cout<<"***************************************"<<endl;  
 //元素的搜索find(),pair<iterator,iterator>equal_range(const key_type &k)const  
    //和multiset的用法一样  
 multimap<int,char*>::iterator s;  
 s=m.find(1);//find()只要找到一个就行了，然后立即返回。  
 cout<<(*s).second<<"    "  
  <<(*s).first<<endl;  
 cout<<"键值等于1的元素个数是："<<m.count(1)<<endl;  
 cout<<"***************************************"<<endl;  
 //删除 erase(),clear()  
 m.erase(1);  
    for(i=m.begin();i!=iend;i++)  
 {  
  cout<<(*i).second<<"的价钱是"  
   <<(*i).first<<"元/斤\n";  
 }  
    return 0;  
}  
