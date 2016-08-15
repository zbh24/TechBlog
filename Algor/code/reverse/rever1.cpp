//普通方法实现链表的逆置
void reverseList(pNode *head)
{
	pNode p, q, r;
	if (*head == NULL || (*head)->next == NULL)
		return;
	q = *head;
	p = q->next;
	r = NULL;
	while (p){
		q->next = r;
		r = q;
		q = p;
		p = p->next;
	}
	q->next = r;
	*head = q;
}

//递归法实现链表的逆置
pNode reverseList_reverse(pNode head)
{
	pNode current_head, head_next;
	if (head == NULL)
		return NULL;
	
	if (head->next == NULL)//边界条件
		return head;
	else{
		current_head = head;//记下当前的头结点a0
		head_next = head->next;//记下当前头结点后面的结点a1
		head = reverseList_reverse(head_next);//返回(a1...an)逆转后的头结点
		head_next->next = current_head;//用上面保存的地址（逆转后的尾结点）指向原来的头结点a0
		current_head->next = NULL;//将a0的next域置零
	}
	return head;//返回a0
}
