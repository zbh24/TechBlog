

// SPEC AND secmtranics
// return value: return all the sub tree's sum
 
int subSum(TreeNode *root,int &maxSum) {
  int left,right,sum;
  if (root == NULL)
    return 0;

  left = subSum(root->left,maxSum);
  right = subSum(root->right,maxSum);
  sum = left + right + root->val;
  maxSum = max(maxSum,sum);
  return sum;
}

int main() {
  int result = INT_MIN;
  subSum(root,result);
  return result;
}
