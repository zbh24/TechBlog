#include<iostream>
using namespace std;

//二叉树复制和左右子树互换

class BTNode  
{  
public:  
	char data;  
	BTNode *lChild;  
	BTNode *rChild;  

	BTNode(char c)  
	{  
		data = c;  
	}  
};  

void Create(BTNode *&t)  
{  
	char c;  
	cin>>c; 
	if(c == '#')  
		t = NULL;  
	else  
	{  
		t = new BTNode(c);  
		t->lChild = NULL;  
		t->rChild = NULL;  
		Create(t->lChild);  
		Create(t->rChild);  
	}  
}  
//交换左右子树
void Swap(BTNode *&t)
{
	if(t)
	{
		if(t->lChild != NULL || t->rChild != NULL)
		{
			BTNode *tmp = t->lChild;
			t->lChild = t->rChild;
			t->rChild = tmp;
		}
		Swap(t->lChild);
		Swap(t->rChild);
	}
}



BTNode* swap (BTNode *root) {
  if(root == NULL)
    return NULL;

  Node *left,*right;
  if (root->lChild == NULL && root->rChild == NULL)
    return root;

  left = right = NULL;
  left = swap(root->lChild);
  right = swap(root->rChild);

  root->lChild = right;
  root->lChild= left;
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
//层次遍历
void LevelOrder(BTNode *&t)
{
	int front = 0, rear = 1;
	BTNode *p[100];
	p[0] = t;
	while(front < rear)
	{
		if(p[front])
		{
			cout<<" "<<p[front]->data; 
			p[rear++] = p[front]->lChild;
			p[rear++] = p[front]->rChild;
			front ++;
		}
		else
			front ++;
	}
}

int main()
{
	BTNode *p1, *p2;
	char c;
	Create(p1); Create(p2);
	cin>>c;

	BTNode *t = new BTNode(c);
	t->lChild = p1; t->rChild = p2;

	cout<<"PreOrder:";
	PreOrder(t);
	cout<<endl;

	cout<<"LevelOrder:";
	LevelOrder(t);
	cout<<endl;

	Swap(t);

	cout<<"PreOrder:";
	PreOrder(t);
	cout<<endl;

	cout<<"LevelOrder:";
	LevelOrder(t);
	cout<<endl;

	return 0;
}
