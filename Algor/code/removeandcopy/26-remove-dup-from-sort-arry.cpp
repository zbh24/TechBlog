class Solution {
public:
    int removeDuplicates(vector<int>& nums) {
      int size;
      int i,j;
      
      size = nums.size();
      if (size == 0)
	return 0;
      i = j = 0;
      for (; i < size; i++) {
	if (nums[i] != nums[j]) {
	  j++;
	  nums[j] = nums[i];
	}
      }
      return j+1;
    }
};
