class Solution {
public:
    vector<vector<int>> combinationSum3(int k, int n) {
      vector<vector<int> > res;
      vector<int> tmp;
      vector<int> candidates;

      for(int i = 1;i <= 9;i++)
	candidates.push_back(i);
      backtrace(candidates,n,res,tmp,0,0,k);
      return res;  
    }

  void backtrace(vector<int>& cand,int target,vector<vector<int> >& res,vector<int>& tmp,int start,int count,int k) {
    if (!target && count == k) {
      res.push_back(tmp);
      return ;
    }

    for(int i = start;i < cand.size() && target >= cand[i];i++) {
      tmp.push_back(cand[i]);
      backtrace(cand,target-cand[i],res,tmp,i+1,count+1,k);
      tmp.pop_back();
    }
  }
};
