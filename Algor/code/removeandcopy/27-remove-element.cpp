class Solution {
public:
    int removeElement(vector<int>& nums, int val) {
      int size;
      int i,j;

      size = nums.size();
      if (size == 0)
	return 0;
      i = j = 0;
      for(;i < size;i++) {
	if(nums[i] != val) {
	  nums[j] = nums[i];
	  j++;
	} 
      }
      return j;
    }
};
