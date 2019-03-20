class Solution {
public:
    vector<int> preorderTraversal(TreeNode* root) {
      vector<int> res;
      stack<TreeNode*> st;

      TreeNode *temp;
      temp = root;
      while (!st.empty() || temp != NULL) {
        while (temp != NULL) {
          st.push(temp);
          temp = temp->left;
        }
        if (!st.empty()) {
          TreeNode *x = st.top();
          st.pop();
          res.push_back(x->val);
          temp = x->right; 
        }
      }
      return res;
    }
};

