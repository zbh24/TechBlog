int father[50005], num[50005];
 
void makeSet(int n) {
    for(int j = 1; j <= n; j++)
    {
        father[j] = j;
        num[j] = 1;
    }
}

int findSet(int x) {
    if(father[x] != x) 
    {    
        father[x] = findSet(father[x]);
    }
    return father[x]; 
}

void Union(int a, int b) {
    int x = findSet(a);
    int y = findSet(b);
    if(x == y) {
        return;
    }
    if(num[x] <= num[y])
    {
        father[x] = y;
        num[y] += num[x];
    }
    else 
    {
        father[y] = x;
        num[x] += num[y];
    }
}
