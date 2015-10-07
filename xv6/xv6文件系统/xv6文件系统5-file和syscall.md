#File descriptor layer
文件描述符的代码
```
struct file {
enum { FD_NONE, FD_PIPE, FD_INODE } type;
int ref; // reference count
char readable;
char writable;
struct pipe *pipe;
struct inode *ip;
uint off;
};
```
每次调用都会open一个新的struct file
每个打开的文件在内存里面，放在一个global file table，（ftable），分配一个文件filealloct，复制一个呢filedup，释放一个fileclose，还有写和读fileread，filewrite。
```
// Allocate a file structure.
struct file*
filealloc(void)
{
	struct file *f;
	acquire(&ftable.lock);
	for(f = ftable.file; f < ftable.file + NFILE; f++)
	{
		if(f−>ref == 0){
			f−>ref = 1;
			release(&ftable.lock);
			return f;
		}
	}
	release(&ftable.lock);
	return 0;
}

// Increment ref count for file f.
struct file*
filedup(struct file *f)
{
	acquire(&ftable.lock);
	if(f−>ref < 1)
		panic("filedup");
	f−>ref++;
	release(&ftable.lock);
	return f;
}

// Close file f. (Decrement ref count, close when reaches 0.)
void
fileclose(struct file *f)
{
	struct file ff;
	acquire(&ftable.lock);
	if(f−>ref < 1)
		panic("fileclose");
	if(−−f−>ref > 0){
		release(&ftable.lock);
		return;
	}
	ff = *f;
	f−>ref = 0;
	f−>type = FD_NONE;
	release(&ftable.lock);
	if(ff.type == FD_PIPE)
		pipeclose(ff.pipe, ff.writable);
	else if(ff.type == FD_INODE){
		begin_trans();
		iput(ff.ip);
		commit_trans();
	}
}
```
对于filestat，fileread，filewrite
```
// Get metadata about file f.
int
filestat(struct file *f, struct stat *st)
{
	if(f−>type == FD_INODE){
		ilock(f−>ip);
		stati(f−>ip, st);
		iunlock(f−>ip);
		return 0;
	}
	return −1;
}

// Read from file f.
int
fileread(struct file *f, char *addr, int n)
{
	int r;
	if(f−>readable == 0)
		return −1;
	if(f−>type == FD_PIPE)
			return piperead(f−>pipe, addr, n);
	if(f−>type == FD_INODE){
		ilock(f−>ip);
		if((r = readi(f−>ip, addr, f−>off, n)) > 0)
			f−>off += r;
		iunlock(f−>ip);
		return r;
	}
	panic("fileread");
}
```

#System calls
sysfile.c里面有一个系统调用值得一看的。
sys_link 和sys_unlink值得好好一看
统计这个文件:
- grep -rn "" ./ | wc -lwc
- grep -rn " " *.c *.h | wc -lwc
- grep -rn "^$" *c *.h | wc -lwc
- 

PS:
```
zbh@zbh-Latitude-E5440:~/test$ grep -rn "" test 
1:It is a test char.From the 2th line,it is a tab,space,newling,abcABC
2:	
3: 
4:
5:abcABC
zbh@zbh-Latitude-E5440:~/test$ grep -rn " " test 
1:It is a test char.From the 2th line,it is a tab,space,newling,abcABC
3: 
zbh@zbh-Latitude-E5440:~/test$ grep -rn "^$" test 
4:
```
