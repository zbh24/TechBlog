/**
 * Definition for a binary tree node.
 * struct TreeNode {
 *     int val;
 *     TreeNode *left;
 *     TreeNode *right;
 *     TreeNode(int x) : val(x), left(NULL), right(NULL) {}
 * };
 */
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

    TreeNode* buildTree(vector<int>& inorder, vector<int>& posorder) {
      int size1 = inorder.size();
      int size2 = posorder.size();
     
      if (!size1 || !size2)
        return NULL;
      find_loc(inorder); 
      return qsort(posorder);
    }
    
    TreeNode* qsort(vector<int>& posorder) {
      int size = posorder.size();
      if(!size)
        return NULL; 
      TreeNode* head = new TreeNode(posorder[size-1]);
      vector<int> left,right;
      int k = loc[posorder[size-1]];
      for (int i = 0; i < posorder.size() - 1;i++)
        if (loc[posorder[i]] < k)
          left.push_back(posorder[i]);
        else
          right.push_back(posorder[i]);
      head->left = qsort(left);
      head->right = qsort(right);
      return head;
    }
};

