#include<iostream>
#include<stack>
#include<vector>

using namespace std;

    string reverseStr(vector<string> str)
    {
      string s;
      for (int i = str.size() - 1; i >= 0; i--) {
        s += str[i];
      }
      return s;
    }

    string repeateFunc(string str, int num)
    {
      string s;
      for (int i = 0; i < num; i++) {
        s += str;
      }
      return s;
    }


string UnzipString(string records)
    {
      int len = records.size();
      if (len == 0 || len == 1) {
        return records;
      }
      string ans;
      stack<string> st1;

      string temp;
      for (int i = 0; i < len;) {
        if (records[i] == '(') {
          if (temp.size() != 0 && temp != "") {
            st1.push(temp);
          }
          st1.push("(");
          temp.clear();
          i++;
        } else if (records[i] >= 'a' && records[i] <= 'z') {
           temp += records[i];
           i++;
        } else if (records[i] == ')') {
          i += 2;
          int repeateNum = 0;
          if (records[i] >= '2' && records[i] <= '9') {
            repeateNum = records[i] - '0';
            i += 2;
          } else {
            i += 3;
            repeateNum = 10;
          }
          vector<string> st2;
          while (st1.size() > 0) {
            if (st1.top().size() == 1 && st1.top() == "(") {
              st1.pop();
              break;
            }
            st2.push_back(st1.top());
            st1.pop();
          }
          string inputString = reverseStr(st2) + temp;
          string sRepeate = repeateFunc(inputString, repeateNum);
          temp.clear();
          st1.push(sRepeate);
        }
      }
      st1.push(temp);
      vector<string> tempStr;
      while (st1.size() > 0) {
        tempStr.push_back(st1.top());
        st1.pop();
      }
      ans = reverseStr(tempStr);
      return ans;
    }

int main() {
  cout << UnzipString("a(b(c)<3>d)<2>e");
}
