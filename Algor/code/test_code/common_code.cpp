
bool hash_code(Node *root,Node *p) {
  if (p == NULL || root == NULL)
    return false;
  
  if (root == p)
    return true;
  return hash_code(root->left,p) || hash_code(root->right,p);
}

Node* commmon_code(Node *root,Node *p,Node *q) {
  if(hash_code(root->left,p) && hash_code(root->left,q))
    return common_code(root->left,p,q);

  if(hash_code(root->right,p) && hash_code(root->right,q))
    return common_code(root-right,p,q);
  
  return root;
}


bool GetNodePath(Node *root,Node *p,vector<Node *>& path) {
  if (root == p)
    return true;

  bool flag = false;
  
  if (root->left != NULL) {
    path.push_back(root);
    flag = GetNodePath(root->left,p,path);
  }
  if(!flag && root->right != NULL)
    flag = GetNodePath(root->right,p,path);

  if(root->left == NULL && right == NULL)
    return false;

  if (!flag)
    return false;
  
  return true;
}





bool flag = false;
void GetNodePath(Node *root,Node *p,vector<Node *>& path) {
  if (flag == true)
    return;
  
  if (root == p) {
    flag = true;
    return ;
  }
  
  if (root->left != NULL) {
    if (flag == false) {
      path.push_back(root);
      GetNodePath(root,p,path);
    }
    if (!flag)
      path.pop_back();
  }

  if (root->right != NULL) {
    if (flag == false) {
      path.push_back(root);
      GetNodePath(root->right,p,path);
    }
    if (!flag)
      path.pop_back();
  }
  return;
}

Node* last_common_node(Node *root,Node *p,Node *q) {
  vector<Node*> path1;
  vector<Node*> path2;

  GetNodePath(root,p,path1);
  GetNodePath(root,p,path2);

  Node* tmp1,tmp2;
  Node *res;
  reverse(path1.begin(),path1.end());
  reverse(path2.begin(),path2.end());
  while (path1.size() != 0 && path2.size() != 0) {
    tmp1 = path1.pop_back ();
    tmp2 = path2.pop_back();
    if (tmp1 == tmp2)
      res = tmp1;
    else
      return res;
  }
  return NULL;
}

