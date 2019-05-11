class Solution {
public:
    struct Node {
      string s;
      int freq;
      Node(string s, int freq):s(s),freq(freq) {}
      friend bool operator < (Node a, Node b) {
        if (a.freq != b.freq)
          return a.freq < b.freq;
        else
          return a.s > b.s;
      }
    };  

    vector<string> topKFrequent(vector<string>& words, int k) {
      priority_queue<Node> q;
      unordered_map<string,int> h_map;
      for (int i = 0; i < words.size(); i++) {
        h_map[words[i]]++;  
      }
      for (auto item : h_map) {
        Node *p = new Node(item.first, item.second);
        q.push(*p);
      }
      vector<string> res;
      while (k-- > 0) {
        res.push_back(q.top().s);
        q.pop();
      }
      return res;
    }
};

