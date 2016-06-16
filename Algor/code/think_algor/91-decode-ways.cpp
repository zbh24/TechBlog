
// Recursion version
class Solution {
public:
    
  void dfs(int& len,string& s ,int pos,int& count) {
    if (pos == len) {
      count++;
      return ;
    }
      
    if (pos < len) {
       int x = s[pos]-'0';
       if (x >= 1 && x <= 26)
	dfs(len,s,pos+1,count);
    }

    if (pos + 1 < len) {
      int x0 = s[pos] - '0';
      int x1 = s[pos+1] - '0';
      int x = x0*10+x1;
      if (x0 == 0)
	return;
      if (x >= 1 && x <= 26)
	dfs(len,s,pos+2,count);  
     } 
  }


  int numDecodings(string s) {
    int count = 0;
        int len;
    if (s == "")
      return 0;
    len = s.length();
    dfs(len,s,0,count);
    return count;
  }
};


class Solution {
public:


  
  int numDecodings(string s) {
    int len;
    vector<int> res(10000,0);
    int temp0,temp1;
    int value;
    int count;

    len = s.length();
    if (s == "")
      return 0;
    
    if (len >= 1) {
      int x = s[0] - '0';
      if (x >= 1 && x <= 26)
	res[0] = 1;
      else
	res[0] = 0;
    }

    // dp
    for(int i = 1;i < len;i++) {
      temp1 = s[i] -'0';
      temp0 = s[i-1] -'0';
      value = temp0 * 10 + temp1;
      count = 0;
      if (temp1 >= 1 && temp1 <= 26)
	count += res[i-1];
      if ((temp0 != 0) && (value >= 1 && value <= 26))
	if (i != 1)
	  count += res[i-2];
        else
	  count++;
      res[i] = count;
    }
    return res[s.length()-1];
  }
};












