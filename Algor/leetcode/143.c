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
    void reorderList(ListNode* head) {
      if (head == NULL || head->next == NULL ||
            head->next->next == NULL)
        return;  
      int num = 0;
      ListNode *temp = head;
      while (temp) {
        temp = temp->next;
        num++;
      }
      rec(head, num);
    }

    ListNode *rec(ListNode *head, int k) {
      if (k <= 2)
        return head;  
      ListNode *temp = head;
      int num = k;
      while (k > 2) {
        temp = temp->next;
        k--;
      }
      ListNode *nextele = head->next;
      head->next = temp->next;
      temp->next = NULL;
      head->next->next = rec(nextele, num - 2);
      return head;
    }
};
