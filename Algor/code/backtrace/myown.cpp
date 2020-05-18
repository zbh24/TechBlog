class Solution {
public:
    bool canPartitionKSubsets(vector<int>& nums, int k) {
      int sum = 0;
      for (auto &e : nums) {
        sum += e;
      }

      if (k <= 0) return false;
      if (sum % k != 0) return false;

      vector<bool> visited(nums.size(), false);
      return dfs(nums, visited, 0, k, 0, 0, sum/k);
  }

  bool dfs(vector<int> &nums, vector<bool> &visited, int start, int k, int cur_sum, int cur_num, int target) {
    if (k == 1) {
      return true;
    }

    if (cur_sum > target) return false;
    if (cur_sum == target && cur_num > 0) {
      return dfs(nums, visited, 0, k - 1, 0, 0, target);
    }

    for (int i = start; i < nums.size(); i++) {
      if (visited[i] == false) {
        visited[i] = true;
        if (dfs(nums, visited, i + 1, k, cur_sum + nums[i], cur_num + 1, target)) {
          return true;
	}
	visited[i] = false;
      }
    }
    return false;
  }
};
