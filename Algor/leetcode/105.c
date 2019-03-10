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
    std::map<int,int> loc;
    void find_loc(vector<int> &num) {
      int size = num.size();
      for(int i =0 ;i < size;i++)
        loc[num[i]] = i;
    }

    TreeNode* buildTree(vector<int>& preorder, vector<int>& inorder) {
      int size1 = preorder.size();
      int size2 = inorder.size();
     
      if (!size1 || !size2)
        return NULL;
      find_loc(inorder); 
      return qsort(preorder);
    }
    
    TreeNode* qsort(vector<int>& preorder) {
      if(!preorder.size())
        return NULL; 
      TreeNode* head = new TreeNode(preorder[0]);
      vector<int> left,right;
      int k = loc[preorder[0]];
      for (int i = 1; i < preorder.size();i++)
        if (loc[preorder[i]] < k)
          left.push_back(preorder[i]);
        else
          right.push_back(preorder[i]);
      head->left = qsort(left);
      head->right = qsort(right);
      return head;
    }
};

