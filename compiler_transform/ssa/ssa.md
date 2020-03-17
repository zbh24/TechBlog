1.建立SSA主要是有几步。
1）插入phi点。
2）重命名变量。

2.关于插入phi，主要是计算DOM.主要是计算DOM集合，IDOM，DF.有几个算法。PS:我们说的dom和支配是恰好相反的概念。

- dom表示它支配的集合，就是到达他，必须要经过哪些节点。
  DF表示支配边界,在离开N的每个路径上，第一个到达，但是不支配的的节点，则是支配边界。
  idom表示一个dom结合中最近的，即第一个节点则为idom，
- so the step is: dom --> idom --> df

3.算法实现：
- dom算法：
dom(n) = {n} union (m blong pred dom(m))

- then find the nearest idom

- algor
`
for all node n in the cfg
  df(n) = void

for all nodes n in teh in the cfg
  if n has mult pred p  then
    foeach p of n
      runner = p;
      while runner != idom(n)
        df(ruuner) = df (ruuner) union {n}
	runner = idom(runner)
`