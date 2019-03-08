/**
 * Definition for singly-linked list.
 * struct ListNode {
 *     int val;
 *     ListNode *next;
 *     ListNode(int x) : val(x), next(NULL) {}
 * };
 */
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
    int list_size(ListNode* node) {
      int num = 0;
      while(node != NULL) {
        num++;
        node = node->next;
      }
      return num;
    }
  
    int walk_n(ListNode *node ,int k) {
      while(k-- > 0) {
        node = node->next;
      }
      return node->val;
    }

    TreeNode* sortedListToBST(ListNode* head) {
       int size = list_size(head);
       if (!head)
         return NULL;
       return qsort(head, 0, size-1);
    }
    
    TreeNode* qsort(ListNode* node, int start, int end) {
      if (start > end)
        return NULL;
      int k = (start + end) / 2;
      TreeNode *head = new TreeNode(walk_n(node,k));
      head->left = qsort(node, start, k -1);
      head->right = qsort(node, k + 1, end); 
      return head;
    }
};
