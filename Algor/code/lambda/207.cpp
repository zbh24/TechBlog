class Solution {
public:
    bool canFinish(int numCourses, vector<vector<int>>& prerequisites) {                                                                     
      bool visited[numCourses] = {false};                                                                                                    
      std::map<int, std::set<int> > edges;                                                                                                   
      int degree[numCourses] = {0};                                                                                                            
      int size = prerequisites.size();                                                                                                       
      for (int i = 0; i < size; i++) {                                                                                                       
        vector<int> &temp = prerequisites[i];                                                                                                
        edges[temp[0]].insert(temp[1]);                                                                                                      
        degree[temp[1]]++;                                                                                                                   
      }   
      if (size == 0)
          return true;
      bool flag = true;                                                                                                                      
     auto autoFunc = [&visited, &numCourses] (bool visited[], int len) {
        for (int i = 0;i < len;i++)
          if (visited[i] == false)
	    return true;

        return false;
      };
      while (autoFunc(visited, numCourses)) {
        int v;                                                                                
       	auto findFunc = [&degree, &visited, &numCourses](int &node) {
          for (int i = 0; i < numCourses; i++) {
            if (degree[i] == 0 && visited[i] == false) {
	      node = i;
	      return true;
            }
          }
	  return false;
	};
	
        if (findFunc(v)) {

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
