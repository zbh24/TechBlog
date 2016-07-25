class Solution {
public:
    bool isAnagram(string s, string t) {
      sort(s.begin(),s.end());
      sort(t.begin(),t.end());
      return s==t;
    }
};


//counting sort
public class Solution {
  public boolean isAnagram(String s, String t) {
      int[] alphabet = new int[26];
      for (int i = 0; i < s.length(); i++) alphabet[s.charAt(i) - 'a']++;
      for (int i = 0; i < t.length(); i++) {
        alphabet[t.charAt(i) - 'a']--;
        if(alphabet[t.charAt(i) - 'a'] < 0) return false;
      }
      for (int i : alphabet) if (i != 0) return false;
      return true;
  }
}

/********************************************************/

// most slowly
class Solution {
public:
    bool isAnagram(string s, string t) {
      sort(s.begin(),s.end());
      sort(t.begin(),t.end());
      return s==t;
    }
};

class Solution {
public:
    bool isAnagram(string s, string t) {
        if (s.length() != t.length()) return false;
        int n = s.length();
        unordered_map<char, int> counts;
        for (int i = 0; i < n; i++) {
            counts[s[i]]++;
            counts[t[i]]--;
        }
        for (auto count : counts)
            if (count.second) return false;
        return true;
    }
};

//most quickly,counting sort
class Solution {
public:
    bool isAnagram(string s, string t) {
        if (s.length() != t.length()) return false;
        int n = s.length();
        int counts[26] = {0};
        for (int i = 0; i < n; i++) { 
            counts[s[i] - 'a']++;
            counts[t[i] - 'a']--;
        }
        for (int i = 0; i < 26; i++)
            if (counts[i]) return false;
        return true;
    }
};
