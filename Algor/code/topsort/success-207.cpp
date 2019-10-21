class Solution {
public:
  bool haveNoVisited(bool visited[], int len) {                                                                                              
    for (int i = 0;i < len;i++)                                                                                                              
      if (visited[i] == false)                                                                                                               
        return true;                                                                                                                         
    return false;                                                                                                       
  }                                                                                                                                          
  bool findNode(int degree[], int len, int &node) {                                                                                          
    for (int i = 0; i < len; i++) {                                                                                                          
      if (degree[i] == 0) {                                                                                                                  
        node = i;                                                                                                                            
        return true;                                                                                                                         
      }                                                                                                                                      
    }                                                                                                                                        
    return false;                                                                                                                            
  }                                                                                                                                          
    bool canFinish(int numCourses, vector<vector<int>>& prerequisites) {                                                                     
      bool visited[1001] = {false};                                                                                                    
      std::map<int, std::set<int> > edges;                                                                                                   
      int degree[1001] = {0};                                                                                                            
      int size = prerequisites.size();                                                                                                       
      for (int i = 0; i < size; i++) {                                                                                                       
        vector<int> &temp = prerequisites[i];                                                                                                
        edges[temp[0]].insert(temp[1]);                                                                                                      
        degree[temp[1]]++;                                                                                                                   
      }   
      if (size == 0)
          return true;
      bool flag = true;                                                                                                                      
      while (haveNoVisited(visited, numCourses)) {                                                                                           
        int v;                                                                                                                               
        if (findNode(degree, numCourses, v)) { 
          visited[v] = true;
          for (auto node : edges[v]) {                                                                                                       
            degree[node]--;                                                                                                                  
          }                                                                                                                                  
        } else {                                                                                                                             
          flag = false;                                                                                                                      
          break;                                                                                                                             
        }                                                                                                                                    
      }                                                                                                                                      
      return flag;                                                                                                                           
    }               
};
