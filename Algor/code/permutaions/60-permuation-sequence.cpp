class Solution {
public:

  int  nextPermutation(vector<int>& nums,int size,int k) {
    int tmp,loc;
    while (k > 1) {
    for (int i = size-1; i >= 1;i--) {
      if (nums[i-1] > nums[i]) {
	if (i == 1) {
	  //sort(nums.begin(),nums.end());
	  return 1;  
	}
      }
      if (nums[i-1] < nums[i]) {
	tmp = 0x7fffffff;
	loc = -1;
	for(int j = i;j < size;j++) {
	  if(nums[j] > nums[i-1] && nums[j] < tmp) {
	    loc = j;
	    tmp = nums[j];
	  }
	}
	// right
	swap(nums[loc],nums[i-1]);
	sort(nums.begin()+i,nums.end());
        goto s;
     }
    }
    s:k--;
    }
    return 0;
  }

    string getPermutation(int n, int k) {
      vector<int> res;
      int size;
      string s;


      for(int i = 1;i <= n;i++)
	res.push_back(i);

      size = res.size();      
      nextPermutation(res,size,k);
  
      for (int i=0;i < res.size();i++) {
	s +=std::to_string(res[i]); 
      }
      return s;
    }
};
