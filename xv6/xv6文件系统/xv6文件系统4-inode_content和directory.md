#directoty

```
struct dirent {
	ushort inum;
	char name[DIRSIZ];
};
```
在目录entry中寻找目录
```
// Look for a directory entry in a directory.
// If found, set *poff to byte offset of entry.
struct inode*
dirlookup(struct inode *dp, char *name, uint *poff)
{
	uint off, inum;
	struct dirent de;
	if(dp−>type != T_DIR)
		panic("dirlookup not DIR");
	for(off = 0; off < dp−>size; off += sizeof(de)){
		if(readi(dp, (char*)&de, off, sizeof(de)) != sizeof(de))
			panic("dirlink read");
		if(de.inum == 0)
			continue;
		if(namecmp(name, de.name) == 0){
			// entry matches path element
			if(poff)
				*poff = off;
			inum = de.inum;
			return iget(dp−>dev, inum);
		}
	}
	return 0;
}
```
dirlink添加目录
```
// Write a new directory entry (name, inum) into the directory dp.
int
dirlink(struct inode *dp, char *name, uint inum)
{
	int off;
	struct dirent de;
	struct inode *ip;
	// Check that name is not present.
	if((ip = dirlookup(dp, name, 0)) != 0){
		iput(ip);
		return −1;
	}
	// Look for an empty dirent.
	for(off = 0; off < dp−>size; off += sizeof(de)){
		if(readi(dp, (char*)&de, off, sizeof(de)) != sizeof(de))
			panic("dirlink read");
		if(de.inum == 0)
			break;
	}
	strncpy(de.name, name, DIRSIZ);
	de.inum = inum;
	if(writei(dp, (char*)&de, off, sizeof(de)) != sizeof(de))
		panic("dirlink");
	return 0;
}
```
writei:写到数据块儿里面去。
#inode
bmap:首先，就是先返回第n个disk bock的地址,如果没有，就申请一个。
```
// Return the disk block address of the nth block in inode ip.
// If there is no such block, bmap allocates one.
static uint
bmap(struct inode *ip, uint bn)
{
uint addr, *a;
struct buf *bp;
if(bn < NDIRECT){
if((addr = ip−>addrs[bn]) == 0)
ip−>addrs[bn] = addr = balloc(ip−>dev);
return addr;
}
bn −= NDIRECT;
...
...
```

如果没目录引用，并且也没有内存引用，那么就把这个给inode的数据块儿给释放了。
```
/ Truncate inode (discard contents).
// Only called when the inode has no links
// to it (no directory entries referring to it)
// and has no in−memory reference to it (is
// not an open file or current directory).
static void
itrunc(struct inode *ip)
{
int i, j;
struct buf *bp;
uint *a;
for(i = 0; i < NDIRECT; i++){
if(ip−>addrs[i]){
bfree(ip−>dev, ip−>addrs[i]);
ip−>addrs[i] = 0;
}
}
if(ip−>addrs[NDIRECT]){
bp = bread(ip−>dev, ip−>addrs[NDIRECT]);
a = (uint*)bp−>data;
for(j = 0; j < NINDIRECT; j++){
if(a[j])
bfree(ip−>dev, a[j]);
}
brelse(bp);
bfree(ip−>dev, ip−>addrs[NDIRECT]);
ip−>addrs[NDIRECT] = 0;
}
ip−>size = 0;
iupdate(ip);
}
```
readi和writei
```
// Read data from inode.
int
readi(struct inode *ip, char *dst, uint off, uint n)
{
	uint tot, m;
	struct buf *bp;
	if(ip−>type == T_DEV){
		if(ip−>major < 0 || ip−>major >= NDEV || !devsw[ip−>major].read)
			return −1;
		return devsw[ip−>major].read(ip, dst, n);
	}
	if(off > ip−>size || off + n < off)
		return −1;
	if(off + n > ip−>size)
		n = ip−>size − off;
	for(tot=0; tot<n; tot+=m, off+=m, dst+=m){
		bp = bread(ip−>dev, bmap(ip, off/BSIZE));
		m = min(n − tot, BSIZE − off%BSIZE);
		memmove(dst, bp−>data + off%BSIZE, m);
		brelse(bp);
	}
	return n;
}
```
> 至于检查这是因为数据可能不在文件系统里面
if(ip−>type == T_DEV)

stati把inode数据stat数据结构里面，因为系统调用可能会用到。实际上，它不止拷贝了inode的数据，而根据别的拷贝了一些
```
struct Stat {
	char st_name[MAXNAMELEN];
	off_t st_size;
	int st_isdir;
	struct Dev *st_dev;
};
```
