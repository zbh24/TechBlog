class Solution {
public:
    int evalRPN(vector<string>& tokens) {
      int size = tokens.size();
      if (size == 0)
        return  0;
      stack<int> st;
      for (int i = 0;i < size; i++) {
        string temp = tokens[i];
        if (temp.length() == 1 && !(temp[0] >='0' && temp[0] <= '9')) {
          int first = st.top();
          st.pop();
          int second = st.top();
          st.pop();
          int res; 
          if (temp[0] == '+')
            res = first + second; 
          else if (temp[0] == '-')
            res = second - first; 
          else if (temp[0] == '/')
            res = second / first ; 
          else if (temp[0] == '*')
            res = first *  second; 
          st.push(res);
        } else {
          int num = atoi(temp.c_str());
          st.push(num);
        }
      }
      return st.top();
    }
};

