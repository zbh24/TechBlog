class Solution {
public:
    vector<vector<string>> groupAnagrams(vector<string>& strs) {
      unordered_map<string,multiset<string> > mp;
      vector<vector<string> > res;

      for (auto s : strs) {
	string t = s;
	sort(t.begin(),t.end());
	mp[t].insert(s);
      }
      for (auto m :mp) {
	vector<string> temp(m.second.begin(),m.second.end());
	res.push_back(temp);
      }
      return res;
    }
};


string strSort(string& s) {
        int count[26] = {0}, n = s.length();
        for (int i = 0; i < n; i++)
            count[s[i] - 'a']++;
        int p = 0;
        string t(n, 'a');
        for (int j = 0; j < 26; j++)
            for (int i = 0; i < count[j]; i++)
                t[p++] += j;
        return t;
    } 

class Solution {
public:
    vector<vector<string>> groupAnagrams(vector<string>& strs) {
      unordered_map<string,vector<string> > mp;
      vector<vector<string> > res;

      for (auto s : strs) {
	string t = s;
	sort(t.begin(),t.end());
	mp[t].push_back(s);
      }
      for (auto m :mp) {
	vector<string> temp(m.second.begin(),m.second.end());
	res.push_back(temp);
      }
      return res;
    }
};
