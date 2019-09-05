class Solution {
public:
    vector<int> diffWaysToCompute(string input) {
    vector<int> res;

      for (int i = 0; i < input.size();i++) {
	if (input[i] == '+' || input[i] == '-' || input[i] == '*') {
	  vector<int> left = diffWaysToCompute(input.substr(0,i));
	  vector<int> right = diffWaysToCompute(input.substr(i+1));
	  for (auto leftNum : left)
	    for (auto rightNum : right)
              if (input[i] == '+')
		res.push_back(leftNum + rightNum);
	      else if (input[i] == '-')
		res.push_back(leftNum - rightNum);
	      else
		res.push_back(leftNum * rightNum);
	}
      }
      if (res.empty()) {
        res.push_back(atoi(input.c_str()));
      }
      return res;
    }
};
