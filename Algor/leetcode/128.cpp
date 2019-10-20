class Solution {
public:
    int longestConsecutive(vector<int>& nums) {
      int dp[10001] = {0};
      sort(nums.begin(), nums.end());
      int res = 0;
      int size = nums.size();
      if (size > 0) {
        dp[0] = 1;
      }
      res = max(dp[0], res);
      for (int i = 1;i < size; i++) {
        if (nums[i] == nums[i-1] + 1) {
	  dp[i] =  dp[i-1] + 1;
	  res = max(dp[i], res);
	} else if (nums[i] == nums[i-1]) {
	  dp[i] = dp[i-1];
        } else {
          dp[i] = 1;
	}
      }
      return res;
    }
};
