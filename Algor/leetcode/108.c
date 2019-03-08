/**
 * Definition for a binary tree node.
 * struct TreeNode {
 *     int val;
 *     TreeNode *left;
 *     TreeNode *right;
 *     TreeNode(int x) : val(x), left(NULL), right(NULL) {}
 * };
 */
class Solution {
public:
    TreeNode* sortedArrayToBST(vector<int>& nums) {
      int size = nums.size();
      if (size == 0)
        return NULL;    
      return qsort(nums, 0, size-1);
    }

    TreeNode* qsort(vector<int>& nums, int start, int end) {
      if (start > end)
        return NULL;
      int k = (start + end) / 2;
      TreeNode *head = new TreeNode(nums[k]);
      head->left = qsort(nums, start, k -1);
      head->right = qsort(nums, k + 1, end); 
      return head;
    }
};
