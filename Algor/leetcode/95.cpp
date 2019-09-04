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
bool flag[1000] = {false};
vector<TreeNode*> generateTrees(int n) {
vector<TreeNode*> tree;
vector<std::string>  res;
std::string cur;
for (int i = 1;i <= n ;i++) {
    cur = std::to_string(i);
    flag[i] = true;
    dfs(res, cur, n-1, n);
    flag[i] = false;
    cur.clear();
}

buildTree(res, tree);
return tree;
}

  void dfs(vector<std::string> &res, std::string cur, int k, int n) {
    if (k == 0) {
      res.push_back(cur);
      return;
    }
    for (int i = 1;i <= n; i++) {
      if (flag[i] == true)
	continue;
      flag[i] = true;
      dfs(res, cur + std::to_string(i), k-1,n);
      flag[i] = false;
    }
}

void buildTree(vector<std::string > &res, vector<TreeNode*> &tree) {
for(string &item : res) {
  TreeNode *root = new TreeNode(item[0] - '0'); 
    for (int i = 1; i < item.length(); i++) {
      TreeNode *node = new TreeNode(item[i] - '0'); 
      InsertNode(root, node);
    }
    tree.push_back(root);
}
    vector<TreeNode*>::iterator it;
std::string res_str;
map<std::string, vector<TreeNode*>::iterator> map_v;
for (it = tree.begin(); it != tree.end();) {
    visitTree(*it, res_str);     
    if (map_v.find(res_str) != map_v.end()) {
    it = tree.erase(it);	
    } else {
    map_v[res_str] = it;
    it++;
    }
    res_str.clear();
}
}

  void InsertNode(TreeNode *root, TreeNode *node) {
    if (root == NULL)
      return;
    if (root->val < node->val) {
      if (root->right == NULL)
	root->right = node;
      else
	InsertNode(root->right, node);
    } else if (root->val > node->val) {
      if (root->left == NULL)
	root->left = node;
      else
	InsertNode(root->left, node);
    }


}

void visitTree(TreeNode *tree, std::string &res) {
  if (tree) {
   res += std::to_string(tree->val);
   visitTree(tree->left, res);
   visitTree(tree->right, res);
}
}
};
