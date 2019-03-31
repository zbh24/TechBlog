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
    bool hasCycle(ListNode *head, ListNode **pos) {
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
        if (first == second) {
          pos = first;
          return true;
        }
      }
      return false;
    }

    ListNode *detectCycle(ListNode *head) {
      ListNode *pos;
      if (!hasCycle(head, &pos))
        return NULL;
      ListNode *temp;
      int count_pos = 0;
      int count_res = 0;
      ListNode *res =  head;
      while (1) {
        temp = res;
        count_res = count_pos = 0;
        while (count_pos < 2) {
          if (temp == pos)
            count_pos++;
          if (temp == res)
            count_res++;
          temp = temp->next;
        }
        if (count_res == 2)
          return res;
        else
          res = res->next;
      }
    }
};

