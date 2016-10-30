# SQL简单语法

标签（空格分隔）： 未分类

---

1.当你应用 GROUP BY 的时候， SELECT 后没有使用聚合函数的列，都要出现在 GROUP BY 后面。
```
SELECT A.x, A.y, SUM(A.z)
FROM A
GROUP BY A.x, A.y
```

3.
```
LEFT JOIN 关键字会从左表 (table_name1) 那里返回所有的行，即使在右表 (table_name2) 中没有匹配的行。
SELECT column_name(s)
FROM table_name1
LEFT JOIN table_name2 
ON table_name1.column_name=table_name2.column_name
```

4.Join有内连接 和外连接
最普通的就是内链接
inner join和join是一样的。

```
SELECT Persons.LastName, Persons.FirstName, Orders.OrderNo
FROM Persons, Orders
WHERE Persons.Id_P = Orders.Id_P 


SELECT Persons.LastName, Persons.FirstName, Orders.OrderNo
FROM Persons
INNER JOIN Orders
ON Persons.Id_P = Orders.Id_P
ORDER BY Persons.LastName
```




