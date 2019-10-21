class Solution {
public:
    vector<int> maxSlidingWindow(vector<int>& nums, int k) {
      vector<int> res;
      int value= -10001;
      for (int i = 0; i < k;i++) {
        value = max(value, nums[i]);	
      }
      res.push_back(value);
      int temp = value;
      for (int i = k; i < nums.size(); i++) {
	if (nums[k] >= temp) {
          temp = nums[k];
          res.push_back(temp);
	} else if (nums[k-1] = ) {

	}
      }
    }
};
