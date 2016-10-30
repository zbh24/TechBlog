#include <iostream> 
#include <string> 
#include <sstream>      //要使用stringstream流应包含此头文件 
using namespace std; 

int main() 
{ 
stringstream stream;     //声明一个stringstream变量 
int n; 
string str; 

 //string转int 
 stream << "1234";     //向stream中插入字符串"1234" 
 stream >> n;     //从stream中提取刚插入的字符串"1234"  并将其赋予变量n完成字符串到int的转换 
 cout << n << endl;     //输出n 

 stream.clear();     //同一stream进行多次转换应调用成员函数clear 

 //int转string 
 stream << 1234;     //向stream中插入整型数1234 
 stream >> str;     //从steam中提取刚插入的整型数   并将其赋予变量str完成整型数到string的转换 
 cout << str << endl;     //输出str 
 return 0; 
} 
