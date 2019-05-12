class Solution {
public:
    int smallestDistancePair(vector<int>& nums, int k) {
       sort(nums.begin(),nums.end());
       int left= 0;
       int right= nums[nums.size()-1] - nums[0];
       while(left < right){
           int mid = (left + right) / 2;
           int j = 0;
           int count = 0;
           for(int i = 0 ; i < nums.size()  ; i++){
               while(j < nums.size() && nums[j] - nums[i] <= mid) j++;
               count += j - i - 1;
           }
           
           if(count < k){
               left = mid + 1;
           }else{
               right = mid;
           }
       }
       return left;}
};

