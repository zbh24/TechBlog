class Solution {
public:
    vector<vector<int>> combinationSum(vector<int>& candidates, int target) {
      vector<vector<int> > res;
      vector<int> tmp;
      sort(candidates.begin(),candidates.end());
      backtrace(candidates,target,res,tmp,0);
      return res;
    }

  void backtrace(vector<int>& cand,int target,vector<vector<int> >& res,vector<int>& tmp,int start) {
    if (!target) {
      res.push_back(tmp);
      return ;
    }

    for(int i = start;i < cand.size() && target >= cand[i];i++) {
      tmp.push_back(cand[i]);
      //backtrace(cand,target-cand[i],res,tmp,start);
      backtrace(cand,target-cand[i],res,tmp,i);
      tmp.pop_back();
    }
  }
};
