class Solution {
public:
    vector<int> postorderTraversal(TreeNode* root) {
      vector<int> res;
      stack<TreeNode*> st;

      TreeNode *temp;
      temp = root;
      while (temp) {
        st.push(temp);
        temp = temp->left;
      }
      TreeNode *pvisit;
      while (!st.empty()) {
        temp = st.top();
        st.pop();      
      
        if (temp->right == NULL || temp->right == pvisit) {
          res.push_back(temp->val);
          pvisit = temp;
        } else if (temp->right != NULL) {
          st.push(temp);
          temp = temp->right;
          while (temp) {
            st.push(temp);
            temp = temp->left;
          }
        }
      }
      return res;
    }
};

