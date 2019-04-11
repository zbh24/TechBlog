struct Node {
  int key;
  int val;
  struct Node *next;
  struct Node *prev;
  Node():key(0),val(0),next(NULL),prev(NULL) {}
};

class LRUCache {
private:
  unordered_map<int, Node*> h_map;
  Node *head;
  Node *tail;
  int size;
  int capacity;

private:
 void removeNode(Node *node);
 void appendTail(Node *node);

public:
 LRUCache(int capacity);
 ~LRUCache();
 int get(int key);
 void put(int key, int value);
};

LRUCache::LRUCache(int capacity) {
  this->size = 0;
  this->capacity = capacity;
  head = new Node();
  tail = new Node();
  head->next = tail;
  tail->prev = head;
}

LRUCache::~LRUCache() {
  delete head;
  delete tail;
}

void LRUCache::removeNode(Node *p) {
  p->prev->next = p->next;
  p->next->prev = p->prev;
}

void LRUCache::appendTail(Node *p) {
  Node *tmp = tail->prev;
  p->next = tail;
  p->prev = tmp;
  tmp->next = p;
  tail->prev = p;
}

int LRUCache::get(int key) {
   if (h_map.find(key) != h_map.end()) {
     Node *p = h_map[key];
     removeNode(p);
     appendTail(p);
     return p->val;
   }
   return -1;
}

void LRUCache::put(int key, int value) {
  if (h_map.find(key) == h_map.end()) {
    Node *p = new Node();
    p->key = key;
    p->val = value;
    appendTail(p);
    size++;
    h_map[key] = p;
    if (size > capacity) {
      h_map.erase(head->next->key);
      Node *tmp = head->next;
      removeNode(head->next);
      delete tmp;
      size--;
    }
    return ;
  }
  Node *p = h_map[key];
  p->val = value;
  removeNode(p);
  appendTail(p);
  return;
}

