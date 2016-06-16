class Solution {
public:

  int nextPermutation(vector<int>& nums) {
    int size;
    size = nums.size();

    for (int i = size-1; i >= 1;i--) {
      if (nums[i-1] >= nums[i] && i == 1) {
	  return 1;  
	}
      
      
      if (nums[i-1] < nums[i]) {
	int tmp = 0x7fffffff;
	int loc = -1;
	for(int j = i;j < size;j++) {
	  if(nums[j] > nums[i-1] && nums[j] < tmp) {
	    loc = j;
	    tmp = nums[j];
	  }
	}
	// right
	swap(nums[loc],nums[i-1]);
	sort(nums.begin()+i,nums.end());
	return 0;
     } 
    }
    return 0;
  }

    vector<vector<int>> permuteUnique(vector<int>& nums) {
      vector<vector<int> > res;
      int size;
      size = nums.size();

      sort(nums.begin(),nums.end());
      if (size == 1) {
	res.push_back(nums);
	return res;
      }
      res.push_back(nums);
      while (nextPermutation(nums) != 1)
	res.push_back(nums);

      return res;
    }
};
