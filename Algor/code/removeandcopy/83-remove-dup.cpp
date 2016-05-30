/**
 * Definition for singly-linked list.
 * struct ListNode {
 *     int val;
 *     ListNode *next;
 *     ListNode(int x) : val(x), next(NULL) {}
 * };
 */
class Solution {
public:
    ListNode* deleteDuplicates(ListNode* head) {
      ListNode *p,*q;

      p = q = head;
      if (head == NULL)
	return NULL;
      while (q != NULL) {
	if(p->val != q->val) {
	  p = p->next;
	  p->val = q->val;
	}
	q = q->next;
      }
      p->next = NULL;
      return head;
    }
};
