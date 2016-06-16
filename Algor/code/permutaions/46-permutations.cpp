class Solution {
public:

  int  nextPermutation(vector<int>& nums) {
    int size;
    size = nums.size();

    for (int i = size-1; i >= 1;i--) {
      if (nums[i-1] > nums[i]) {
	if (i == 1) {
	  // sort(nums.begin(),nums.end());
	  return 1;  
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
	return 0;
     }
    }
    return 0;
  }
    vector<vector<int>> permute(vector<int>& nums) {
      vector<vector<int>> res;
      if (nums.size() == 1) {
	res.push_back(nums);
	return res;
      }
      sort(nums.begin(),nums.end());
      res.push_back(nums);
      while (nextPermutation(nums) != 1)
	res.push_back(nums);
      return res;
    }
};


//Other solution 
// DFS

   vector<vector<int> > res;
   
int nextPermutation(vector<int>& nums) {
      int size;
      
      size = nums.size();
      if (nums.size() == 1) {
	res.push_back(nums);
	return res;
      }
     sort(nums.begin(),nums.end());
     vector<int> tmp;
     dfs(1,size,tmp);
     return res;
}


bool check(vector<int>& nums,int number,int size) {
  int i;

  for(i = 0;i < size;i++) {
    if(nums[i] == j)
      return false;
  }
  return true;
}
void dfs(int i,int size,vector<int>& nums) {
  
  if (i > size) {
    res.push_back(nums);
    return ;
  }

  for(int j = 1;j <= size;j++) {
    if (check(nums,j,i) == true) {
      nums.push_back(j);
      dfs(i+1,size,nums);
      nums.pop_back();
    }
  }
}



// method 3: recursive dfs
vector<vector<int> > permute(vector<int> &num) {
    vector<vector<int> > ans;
    dfs(num, ans);
    return ans;
}

void dfs(vector<int> &num, vector<vector<int>> &ans) {
    if (num.size() == 1) {
        vector<int> tmp(num.begin(), num.end());
        ans.push_back(tmp);
        return;
    }

    vector<vector<int> > ans1;
    vector<int> num1(num.begin()+1, num.end());
    dfs(num1, ans);

    for(int i = 0; i < ans.size(); ++i) {
        for(int j = 0; j <= ans[i].size(); ++j) {
            vector<int> tmp = ans[i];
            tmp.insert(tmp.begin()+j, num[0]);
            ans1.push_back(tmp);
        }
    }

    ans = ans1;
}


// method 1: standard backtracing solution
vector<vector<int> > permute(vector<int> &num) {
    vector<vector<int> > ans;
    permutation(num, 0, ans);
    return ans;
}

void permutation(vector<int> &num, int begin, vector<vector<int> > &ans) {
    if (begin >= num.size()) {
        ans.push_back(num);
        return;
    }

    // every number chosen to be the begin once
    for (int i = begin; i < num.size(); ++i) {
        swap(num[begin], num[i]);
        permutation(num, begin+1, ans);
        swap(num[begin], num[i]);
    }
}
