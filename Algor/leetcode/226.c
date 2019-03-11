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
    TreeNode* invertTree(TreeNode* root) {
      if (!root)
        return NULL;       
      TreeNode *head = new TreeNode(root->val);
      head->left = invertTree(root->right);
      head->right = invertTree(root->left);
      return head;
    }
};
