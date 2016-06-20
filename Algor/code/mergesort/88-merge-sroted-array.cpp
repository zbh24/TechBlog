class Solution {
public:
    void merge(vector<int>& nums1, int m, vector<int>& nums2, int n) {
      
      int first,second;
      first = second = 0;
      while (first < m && second < n) {
	if(nums1[first] > nums2[second]) {
	  nums1.insert(nums1.begin()+first,nums2[second]);
	  nums1.pop_back();
	  second++;
	} 
	first++;
      }
      if (second < n) {
	while (second < n) {
	  nums1[first++] = nums2[second++];
	}
      }
    }
};

// PASS algorithm 

class Solution {
public:
    void merge(vector<int>& nums1, int m, vector<int>& nums2, int n) {
      int i,j,k;

      i = m-1;
      j = n-1;
      k = m+n-1;

      while (i >= 0 && j >= 0) {
	if (nums1[i] > nums2[j])
	  nums1[k--] = nums1[i--];
	else
	  nums1[k--] = nums2[j--];
      }
      while (j >= 0)
	nums1[k--] = nums2[j--];
    }
};
