class Solution {
public:

  int binserchxia(vector<int>& nums,int target) {
    int low,high,mid;

    low = 0;
    high = nums.size() - 1;

    while (low <= high) {
      mid = low + (high -low) / 2;

      if (nums[mid] < target)
	low = mid + 1;
      else
	high =mid - 1;
    }
    if (nums[low] == target)
      return low;
    return - 1;
  }

  
  int binserchsha(vector<int>& nums,int target) {
    int low,high,mid;

    low = 0;
    high = nums.size() - 1;

    while (low <= high) {
      mid = low + (high -low) / 2;

      if (nums[mid] >  target)
	high = mid - 1;
      else
	low = mid + 1;
    }
    if (nums[high] == target)
      return high;
    return - 1;
  }



    vector<int> searchRange(vector<int>& nums, int target) {
      int low,high;
      vector<int> res;
      low = binserchxia(nums,target);
      high = binserchsha(nums,target);\
      res.push_back(low);
      res.push_back(high);
      return res;
    }
};
