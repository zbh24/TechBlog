

Node* reverse(Node *head) {
  if (head == NULL || head->next = NULL)
    return head;

  Node *p,*q,*r;
  p = head;
  q = p->next;
  p->next = NULL;
 
  while (q != NULL) {
    r = q->next;
    q->next = p;
    p = q;
    q = r;
  }
  head = p;
  return head;
}

Node* reverse_cur(Node *head) {
  if (head == NULL || head->next == NULL)
    return head;

  else {
    Node *p,*q;
    p = head->next;
    q = reverse_cur(p);
    p->next = head;
    head->next = NULL;
    return q;
  }
}


写代码，反转一个单链表，分别以迭代和递归的形式来实现

1.typedef struct node LinkNode;
2.struct node
3.{
4.    int data;
5.    LinkNode*next;
6.};
//返回新链表头节点
LinkNode*reverse_link(LinkNode*head)
LinkNode*reverse_link_recursive(LinkNode*head)

1.//返回新链表头节点
2. LinkNode*reverse_link(LinkNode*head)
3.{
4.    if(head==NULL)
5.      return NULL;
6.    LinkNode*prev,*curr,*reverse_head,*temp;
7.    prev=NULL,curr=head;
8.    while(curr->next)
9.    {
10.      temp=curr->next;
11.      curr->next=prev;
12.      prev=curr;
13.      curr=temp;
14.    }
15.    curr->next=prev;
16.    reverse_head=curr;
17.    return reverse_head;
18.}
19.
20. LinkNode*reverse_link_recursive(LinkNode*head)
21.{
22.    if(head==NULL)
23.      return NULL;
24.    LinkNode*cur,*reverse_head,*temp;
25.    if(head->next==NULL)    //链表中只有一个节点，逆转后的头指针不变
26.      return head;
27.    else
28.    {
29.      curr=head;
30.      temp=head->next;    //temp为(a2,…an)的头指针
31.      reverse_head=reverse_link_recursive(temp);    //逆转链表（a2,…an），并返回逆转后的头指针
32.      temp->next=curr;    //将a1链接在a2之后
33.      curr->next=NULL;
34.    }
35.    return reverse_head;    //(a2,…an)逆转链表的头指针即为(a1,a2,…an)逆转链表的头指针
36.}
