class Solution {
public:
    struct Node {
      int key;
      int freq;
      Node(int key, int freq):key(key),freq(freq) {}
      friend bool operator < (Node a, Node b) {
        return a.freq < b.freq;
      }
    };

    vector<int> topKFrequent(vector<int>& nums, int k) {       
      priority_queue<Node> q;
      unordered_map<int ,int> h_map;
      for (int i = 0; i < nums.size(); i++) {
        h_map[nums[i]]++;  
      }
      for (auto item : h_map) {
        Node *p = new Node(item.first, item.second);
        q.push(*p);
      }
      vector<int> res;
      while (k-- > 0) {
        res.push_back(q.top().key);
        q.pop();
      }
      return res;
    }
};

