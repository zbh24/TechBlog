

// return value :return the all the path sum
//
int subPath(TreeNode *root, int &maxPath) {
  int left,right;
  int sum;
  int Ssum;

  if (root == NULL)
    return 0;

  left = max(0,subPath(root->left,maxPath)); 
  right = max(0,subPath(root->right,maxPath));
  
  // monopath
  sum = max(left,right) + root->val;
  // dualpath
  maxPath = max(maxPath,left+right+root->val);
  
  return sum;
}


