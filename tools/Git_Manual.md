#Git基本教程
####基本概念
git它是一个分布式的版本管理系统，它管理的修改，其实就是linux中的diff程序（最长公共子序列）而不是文件，所以它只能处理文本文件，而二进制文件就不可以了。

git目录里面有个.git，然后这里面存放的是版本库（Repository）（包括暂存区和分支），git分为三个区域：
- 工作区（working directory）:就是，我们能看到的目录
- 暂存区（stage）：git add 以后就到了这儿了
- 分支：git commit提交以后就到了这儿了。默认有个master分支，然后HEAD指向它。

你经常可以用 git status命令来查看当前状态，到底有没有提交
- git status
-  git branch
-  git checkout
-  git checkout -b newbranch

####撤销修改
- git diff:如果暂存区有，就是比较工作区和暂存区，否则就是比较工作区和版本库。
- git diff HEAD -- readme.txt:命令可以查看工作区和版本库里面最新版本的区别
- git checkout -- file:可以丢弃工作区的修改，先回退带到暂存区，暂存区没有，就回退到版本库
- git reset HEAD file可以把暂存区的修改撤销掉（unstage），不修改工作区。

场景1：当你改乱了工作区某个文件的内容，想直接丢弃工作区的修改时，用命令git checkout -- file。

场景2：当你不但改乱了工作区某个文件的内容，还添加到了暂存区时，想丢弃修改，分两步，第一步用命令git reset HEAD file，就回到了场景1，第二步按场景1操作。

场景3：已经提交了不合适的修改到版本库时，想要撤销本次提交，参考版本回退一节，不过前提是没有推送到远程库。

删除：git rm，然后git commit。那么在工作区也看不到这个文件了，不过在历史版本中可以看到。


####关联远程
要关联一个远程库，使用命令git remote add origin https://bitbucket.org./zbh24.git；

关联后，使用命令git push -u origin master第一次推送master分支的所有内容；

此后，每次本地提交后，只要有必要，就可以使用命令git push origin master推送最新修改；

分布式版本系统的最大好处之一是在本地工作完全不需要考虑远程库的存在，也就是有没有联网都可以正常工作，而SVN在没有联网的时候是拒绝干活的！当有网络的时候，再把本地提交推送一下就完成了同步，真是太方便了！
PS:
远程库的名字就是origin，这是Git默认的叫法，也可以改成别的，但是origin这个名字一看就知道是远程库。
关联到具体那个库，你可以看.git/config

由于远程库是空的，我们第一次推送master分支时，加上了-u参数，Git不但会把本地的master分支内容推送的远程新的master分支，还会把本地的master分支和远程的master分支关联起来，在以后的推送或者拉取时就可以简化命令。

####版本控制
在版本回退里，每次提交，Git都把它们串成一条时间线，这条时间线就是一个分支。截止到目前，只有一条时间线，在Git里，这个分支叫主分支，即master分支。HEAD严格来说不是指向提交，而是指向master，master才是指向提交的，所以，HEAD指向的就是当前分支。

一开始的时候，master分支是一条线，Git用master指向最新的提交，再用HEAD指向master，就能确定当前分支，以及当前分支的提交点.

每次提交，master分支都会向前移动一步。

当我们创建新的分支，例如dev时，Git新建了一个指针叫dev，指向master相同的提交，再把HEAD指向dev，就表示当前分支在dev上。

可以发现，Git创建一个分支很快，因为除了增加一个dev指针，改改HEAD的指向，工作区的文件都没有任何变化。

假如我们在dev上的工作完成了，就可以把dev合并到master上。Git怎么合并呢？最简单的方法，就是直接把master指向dev的当前提交，就完成了合并。
git checkout master
git merge dev
//就是把master指针指向dev的了。
注意到上面的Fast-forward信息，Git告诉我们，这次合并是“快进模式”，也就是直接把master指向dev的当前提交，所以合并速度非常快。
git branch -d dev

小结

Git鼓励大量使用分支：

查看分支：git branch

创建分支：git branch <name>

切换分支：git checkout <name>

创建+切换分支：git checkout -b <name>

合并某分支到当前分支：git merge <name>

删除分支：git branch -d <name>

#####如果合并时候有分支冲突
```
$ git merge feature1
Auto-merging readme.txt
CONFLICT (content): Merge conflict in readme.txt
Automatic merge failed; fix conflicts and then commit the result.
```
我们可以查看那些文件，手动进行修改。
Git用<<<<<<<，=======，>>>>>>>标记出不同分支的内容，我们修改如下后保存。

git log
git reflog

####版本回退
现在总结一下：

HEAD指向的版本就是当前版本，因此，Git允许我们在版本的历史之间穿梭，使用命令git reset --hard commit_id。或者回退到上一般本git reset --hard HEAD^。

穿梭前，用git log可以查看提交历史，以便确定要回退到哪个版本。

要重返未来，用git reflog查看命令历史，以便确定要回到未来的哪个版本。

####gitingore
1.创建.gitingore文件，里面写要忽略的文件
2.git add ,git commit上去
以后，就不需要关心了，就不会再提交上去了。
