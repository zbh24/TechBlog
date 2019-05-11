class Solution {
public:
    struct Node {
      int first;
      int second;
      int sum;
      Node(int first,int second,int sum):first(first),second(second),sum(sum) {}
      friend bool operator < (const Node &a, const Node &b) {
        return a.sum > b.sum;
      }
    };
    priority_queue<Node> q;
    set<Node> h_set;
    vector<vector<int>> kSmallestPairs(vector<int>& nums1, vector<int>& nums2, int k) {
      int i,j;
      i = j = 0;
      vector<vector<int>> res;
    
      if (nums1.size() == 0 || nums2.size() == 0 || k == 0)
        return res;
      int sum1,sum2;
      
      for (int i = 0 ;i < nums1.size();i++) {
        Node *p = new Node(i, 0, nums1[i] + nums2[0]);
        q.push(*p);
      }
      while (!q.empty() && k--) {
         int first = q.top().first;
         int second = q.top().second;
         vector<int> temp;
         temp.push_back(nums1[first]);
         temp.push_back(nums2[second]);  
         res.push_back(temp);
         q.pop();
         if (second+1 < nums2.size()) {
           Node *p = new Node(first, second + 1, nums1[first] + nums2[second+1]);
           q.push(*p);
         }
      }
      return res;
    }
};

