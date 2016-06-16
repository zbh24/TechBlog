class Solution {
public:
   vector<vector<int>> combinationSum2(vector<int>& candidates, int target) {
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
      if(i != start && cand[i] == cand[i-1])
	continue;
      tmp.push_back(cand[i]);
      backtrace(cand,target-cand[i],res,tmp,i+1);
      tmp.pop_back();
    }
  }
};
