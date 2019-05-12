class Solution {
public:

    int count1(vector<int> &num, int value) {
      int j = 0;
      int res = 0; 
      for (int i = 0; i < num.size();i++) {
        while (j < num.size() && num[j] <= num[i] + value) 
          j++;
        res += j - i - 1;
      }
      return res; 
    }

    int smallestDistancePair(vector<int>& nums, int k) {
       sort(nums.begin(),nums.end());
       int left= 0;
       int right= nums[nums.size()-1] - nums[0];
       int count = 0;
       while(left <= right){
         int mid = (right+left)/2;
         if (count1(nums,mid) >= k)
          right = mid-1;         
         else
          left = mid + 1;
       }
       return left;
    }
};

