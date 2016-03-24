#include<iostream>
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
		while(low < high && a[high] >= key) //注意要取等号，否则当全部待排序数字都相同的时候会死循环！
			high--;
		swap(a[low],a[high]);
		while(low < high && a[low] <= key ) //pay attention to the equal, otherwise it will get into endless loop!
			low++;
		swap(a[low],a[high]);
	}
	a[low] = key;
	return low;
}

void qsort(int a[], int begin, int end)
{
	int p = partition(a,begin,end);
	if(p > begin)
		qsort(a, begin,p-1);
	if(p < end)
		qsort(a,p+1,end);
}

int findK(int a[],int begin, int end,int k)
{
	if(!(k>=begin && k<= end))
		return 0;
	int p = partition(a,begin,end);
	if(p > k)
		findK(a,begin,p-1,k);
	else if(p < k)
		findK(a,p+1,end,k);
	else if(p == k)
		return a[p];
}

int main()
{
	int a[] = {5,2,3,4,6,8}
	int i;
	int t = partition(a,0,5);
	cout<<t<<endl;
	for(i =0; i<6;i++)
		cout<<a[i]<<' ';
	cout<<endl;
	qsort(a,0,5);
	cout<<"After sorted: "<<endl;
	for(i =0; i<6;i++)
		cout<<a[i]<<' ';
	cout<<endl;
	int k = findK(a,0,5,5);
	cout<<k<<endl;
	return 0;   
}

