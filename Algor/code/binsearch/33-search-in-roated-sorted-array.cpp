class Solution {
public:

  int binsearch(vector<int>& nums,int low,int high,int target) {
    int mid;

    while (low <= high) {
      mid = low + (high -low) / 2;
      if (nums[mid] == target)
	return mid;
      else if (nums[mid] > target)
	high = mid - 1;
      else
	low = mid + 1; 
    }
    return -1;
  }

    int search(vector<int>& nums, int target) {
      int index;
      
      index = -1;
      for (int i = 0;i < nums.size() - 1; i++)
	if(nums[i] > nums[i+1]) {
	  index = i;
	  break;
	}
      if (index == -1)
	return binsearch(nums,0,nums.size()-1,target);

	if (binsearch(nums,0,index,target) != -1)
	  return binsearch(nums,0,index,target);
	else if (binsearch(nums,index+1,nums.size()-1,target) != -1)
	  return binsearch(nums,index+1,nums.size()-1,target);
      else
	return -1;
    }
};
