class Solution {
public:
    int kthSmallest(vector<vector<int>>& num, int k) {
      int low = num[0][0];
      int high = num[num.size()-1][num[0].size()-1];
      while (low < high) {
        int mid = (low + high)/2;
        int i,j;
        int cnt = 0;
        //j = num[0].size()-1;
        for (i = 0; i < num.size();i++) {
        j = 0; 
        while (j < num[0].size() && num[i][j] <= mid)
          j++; 
         cnt += j;
        }
        if (cnt < k)
         low = mid +1;
        else
         high = mid;
    }
    return low;
    }
};

