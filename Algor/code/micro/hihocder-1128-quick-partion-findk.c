#include <iostream>

using namespace std;

void swap(int &a, int &b)
{
	int temp = a;
	a = b;
	b = temp;
}

int partition(int a[],int begin,int end)
{
	int low,high,key;
	low = begin;
	high = end;
	key = a[low];
	while(low < high)
	{
		while(low < high && a[high] >= key) 
			high--;
		swap(a[low],a[high]);
		while(low < high && a[low] <= key )
			low++;
		swap(a[low],a[high]);
	}
	a[low] = key;
	return low;
}

int findnum(int a[],int begin, int end,int num)
{

	int p = partition(a,begin,end);
	
	if (begin > end)
	  return -1;
	if (begin == end && a[begin] != num)
	  return -1;
	
	if (a[p] == num)
	  return p;
	else if(a[p] > num)
	  return findnum(a,begin,p-1,num);
	else
	  return findnum(a,p+1,end,num);
}

int main()
{
        int a[1000010] = {0};
	int n,num;
	cin >> n >>num;
	for(int i = 1;i <= n;i++)
	  cin >> a[i];
	cout<<findnum(a,1,n,num)<<endl;
	return 0;   
}

