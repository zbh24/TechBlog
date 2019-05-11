class Solution {
public:
    struct Node {
      int first;
      int second;
      int sum;
      Node(int first,int second):first(first),second(second),sum(first+second) {}
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
      
      for(int i = 0; i < nums1.size();i++)
        for(int j = 0; j < nums2.size();j++) {
          Node *p = new Node(nums1[i],nums2[j]);
          q.push(*p);
        }
  
      while (!q.empty() && k--) {
        vector<int> temp;
        temp.push_back(q.top().first);
        temp.push_back(q.top().second);
        res.push_back(temp);
        q.pop();
      }
      return res;
    }
};

