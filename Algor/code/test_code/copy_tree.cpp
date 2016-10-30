void dfs(Node *root,int k) {
  if(k > 3)
    return;
  if (k == 3) {
    print(root->val);
    return;
  }
  if(root->left != NULL)
    dfs(root->left,k+1);
  if(root->right != NULL)
    dfs(root->right,k+1);
  return;
}

void bfs(Node *root,int k) {
  if (root == NULL)
    return;

  queue<Node*> q;
  q.push(root);
  Node *t;
  int copunt = 0;
  
  Node *temp;
  temp->data = -1;
  bool flag = false;

  while ( !q.empty() ) {
    t = p.pop();
    
    if (t->data == -1 && q.empty() != 0) {
      q.push(temp);
      k++;
      continue;
    }
    
    if (count > k)
      continue;

    if (count == k)
      cout <<t->data << endl;
    
    if (t->left != NULL)
      q.push(t->left);
    if (t->right != NULL)
      q.push(t->right);
  }
}

Node* swap (Node* root) {
  if(root == NULL)
    return NULL;

  Node *left,*right;
  if (roo->left == NULL && root->right == NULL)
    return root;

  left = right = NULL;
  left = swap(root->left);
  right = swap(root->right);

  root->left = right;
  root->right = left;
  return root;
}




//先序遍历
void PreOrder(BTNode *&t)
{
	if(t)
	{
		cout<<" "<<t->data;
		PreOrder(t->lChild);
		PreOrder(t->rChild);
	}
}


void InOrder(BTNode *&t)
{
	if(t != NULL)
	{
		PreOrder(t->lChild);
	        cout<<" "<<t->data;
		PreOrder(t->rChild);
	}
}

void bfs(Node *root) {
  if (root == NULL)
    return;

  queue<Node*> q;
  q.push(root);
  Node *t;
  while ( !q.empty() ) {
    t = p.pop();
    cout <<t->data << endl;
    if (t->left != NULL)
      q.push(t->left);
    if (t->right != NULL)
      q.push(t->right);
  }
}




