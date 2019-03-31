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
    bool hasCycle(ListNode *head) {
      if (head == NULL)
       return false;    
      ListNode *first, *second;
      first = second = head;
      while (first != NULL && second != NULL) {
        if (first->next != NULL)
          first = first->next;
        else
          return false;
        if (second->next != NULL && second->next->next != NULL)
          second = second->next->next;
        else
          return false;
        if (first == second)
          return true;
      }
      return false;
    }
};
