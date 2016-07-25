class Solution {
public:
 
  bool dfs(vector<vector<char> >& board,string& word,int &row,int &col,int &len,int m,int n,int count) {
    bool tmp;
    if (count == len)
      return true;
    if (m < 0 || n < 0 || m >= row || n >= col)
      return false;
    if (board[m][n] != word[count])
      return false;
    //board[m][n] ^= 256;
    int c = board[m][n];
    board[m][n] = 0;
    tmp = dfs(board,word,row,col,len,m-1,n,count+1) || dfs(board,word,row,col,len,m+1,n,count+1) ||
          dfs(board,word,row,col,len,m,n-1,count+1) || dfs(board,word,row,col,len,m,n+1,count+1);
    //board[m][n] ^= 256;
    board[m][n] = c;
    return tmp;
  }


    bool exist(vector<vector<char>>& board, string word) {
      int m,n;
      int len;
      int count;

      m = board.size();
      n = board[0].size();
      len = word.length();
      count = 0;
      for(int i = 0; i < m;i++)
	for(int j =0;j < n;j++) {
	  if (dfs(board,word,m,n,len,i,j,0) == true)
	    return true;
	}
      return false;
    }
};




 bool dfs(vector<vector<char> >& board,string& word,int &row,int &col,int &len,int m,int n,int count) {
    bool tmp;
    if (count == len)
      return true;
    if (m < 0 || n < 0 || m >= row || n >= col)
      return false;
    if (board[m][n] != word[count])
      return false;
    int c = board[m][n];
    board[m][n] = 0;
    //    tmp = dfs(board,word,row,col,len,m-1,n,count+1) || dfs(board,word,row,col,len,m+1,n,count+1) ||
    //    dfs(board,word,row,col,len,m,n-1,count+1) || dfs(board,word,row,col,len,m,n+1,count+1);
    bool tmp;
    if (tmp = dfs());
    if (!tmp);
    if (!tmp);
    if (!tmp);

    board[m][n] = c;
    return tmp;
  }
