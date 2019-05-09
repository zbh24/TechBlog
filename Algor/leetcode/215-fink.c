class Solution {
public:

    void swap(vector<int> &nums, int a, int b) {
       int temp = nums[a];
       nums[a] = nums[b];
       nums[b] = temp;
    }

    int qsort(vector<int>& nums, int start, int end) {
      int value = nums[start];
      while (start < end) {
        while (start < end && value <= nums[end])
          end--;
        swap(nums,start,end);
        while (start < end && value >= nums[start])
          start++;
        swap(nums,start,end);
      }
      return start;
    }

    int findKthLargest(vector<int>& nums, int k) {
       int len = nums.size();
       int loc = -1;
       loc = qsort(nums,0,len-1);
       k = len -k ;
       // k = k - 1;
       while (loc != k) {
         if (k == loc) {
           return nums[loc];
         } else if (k > loc) {
           loc = qsort(nums,loc+1,len-1);
         } else {
           loc = qsort(nums,0,loc-1);
         }
       }
       return nums[loc];
    }
};

