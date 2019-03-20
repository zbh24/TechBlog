class Solution {
public:
       
 int searchInsert(vector<int>& nums, int target) {
      int low,high,mid;
      
      low = 0;
      high = nums.size() - 1;

      while (low <= high) {
	mid = low + (high-low)/2;
	if(nums[mid] == target)
	  return mid;
	else if (nums[mid] > target)
	  high = mid -1;
	else
	  low = mid + 1;
      }
      // return high+1; thi is  AC too
      // low is should find the elemeent postion
      return low;
    }

};