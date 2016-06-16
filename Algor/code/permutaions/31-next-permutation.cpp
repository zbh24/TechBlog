// This is also right 
class Solution {
public:
  void nextPermutation(vector<int>& nums) {
    int size;
    size = nums.size();

    if (size == 1)
      return ;
    for (int i = size-1; i >= 1;i--) {
      if (nums[i-1] > nums[i]) {
	if (i == 1) {
	  sort(nums.begin(),nums.end());
	  return ;  
	}
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
	return;
     } 
    }
  }
};


//Right
class Solution {
public:

  // void myswap(vector<int>& first ,vector<int>& second) {
  //   int tmp;
  //   tmp = first;
  //   first = second;
  //   second = tmp;
  // }

  void nextPermutation(vector<int>& nums) {
    int size;
    size = nums.size();

    vector<int>::iterator it;

    if (size == 1)
      return ;
    for (it = nums.end()-1; it >= (nums.begin()+1);it--) {
      if (*(it-1) > *it) {
	if (it-1 == nums.begin()) {
	  sort(nums.begin(),nums.end());
	  return ;  
	}
      }
      if (*(it-1) < *it) {
	int tmp = 0x7fffffff;
	vector<int>::iterator p,q;

	for(p = it;p != nums.end();p++) {
	  if(*p > *(it-1) && *p < tmp) {
	    q = p;
	    tmp = *p;
	  }
	}
        swap(*(it-1),*q);
	sort(it,nums.end());
	return;
     } 
    }
  }
};


//Other solution
class Solution {
    void nextPermutation(vector<int>& nums) {
        int k = -1;
        for (int i = nums.size() - 2; i >= 0; i--) {
            if (nums[i] < nums[i + 1]) {
                k = i;
                break;
            }
        } 
        if (k == -1) {
            reverse(nums.begin(), nums.end());
            return;
        }
        int l = -1;
        for (int i = nums.size() - 1; i > k; i--) {
            if (nums[i] > nums[k]) {
                l = i;
                break;
            } 
        } 
        swap(nums[k], nums[l]);
        reverse(nums.begin() + k + 1, nums.end()); 
    }
}; 
