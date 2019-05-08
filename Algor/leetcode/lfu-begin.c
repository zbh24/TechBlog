struct Node {
  int key;
  int val;
  int freq;
  Node():key(0),val(0),freq(0){}
};

class LFUCache {
private:
  unordered_map<int, Node*> h_map;
  unordered_map<int, list<Node*> > list_map;
  unordered_map<int, list<Node*>::iterator> it_map;

  int size;
  int capacity;
  int minifreq;

public:
 LFUCache(int capacity);
 ~LFUCache();
 int get(int key);
 void put(int key, int value);
};

LFUCache::LFUCache(int capacity) {
  this->size = 0;
  this->capacity = capacity;
  minifreq = 0;
}

LFUCache::~LFUCache() {
}

int LFUCache::get(int key) {
   if (h_map.find(key) != h_map.end()) {
     Node *p = h_map[key];
     list_map[h_map[key]->freq].erase(it_map[key]);
     ++(h_map[key]->freq);

     list_map[h_map[key]->freq].push_front(p);
     it_map[p->key] = list_map[h_map[key]->freq].begin();
     if (list_map[minifreq].size() == 0)
       minifreq++;
     return p->val;
   }
   else {
     return -1;
   }
}

void LFUCache::put(int key, int value) {
  if (capacity <= 0)
      return;
  if (get(key) != -1) {
    h_map[key]->val = value;
    return;
  }
    Node *p = new Node();
    p->key = key;
    p->val = value;
    p->freq = 1;
    size++;
    h_map[key] = p;
    list_map[1].push_front(p);
    it_map[key] = list_map[1].begin();
    // to be done
    if (size > capacity) {
      size--;
      Node *temp = list_map[minifreq].back();
      int var = temp->key;

      it_map.erase(var);
      h_map.erase(var);
      list_map[minifreq].pop_back();
    }
    minifreq = 1;
    return ;
}

