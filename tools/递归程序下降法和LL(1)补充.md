# 递归程序下降法和LL(1)补充

标签（空格分隔）： 未分类

---
词法分析的实现：就是识别所有的token，然后返回值和类型，这是标准实现。PS：可以把返回值和类型结合成结构体。

语法分析的实现：就是一个终结符对应一个解析程序，
1)第一个例子：
如
A->1|BA|CA
B->ab
C->a'b'
这种呢，就不需要为非终结符实现一个程序，因为可以直接替换。
```
parse() {
    lex();
    if(token == 1) {
        return;
    } else if(token == a){
        lex();
        if(token == b) {
             parse();
             return;
        }
    } else if(token == a'){
        lex();
        if(token == b') {
	    parse();
            return;
        }
    }
}
```
2)第二个例子：
A->1|BA|CA
B->abB |x(表示为空)
C->a'b'
```
parse() {
    lex();
    if(token == 1) {
        return;
    } else if(token == a){
        lex();
        if(token == b) {
            B();
            return;
        }
    } else if(token == a'){
        lex();
        if(token == b') {
            return;
        }
    }
}

```
这就是词法分析和语法分析的具体过程，可以参考一下。另外呢，关于ENF，主要有3条扩展规则。
[]：表示可选的。
():表示在其中选一
{}:表示可以重复0次或者n次。

这是个补充的题目，有兴趣可以实现一下。

expression = ["+"|"-"] term {("+"|"-"|"OR") term} .

term = factor {( "*" | "/" | "AND" ) factor} .

  factor = 
    func "(" expression ")" 
    | number
    | "(" expression ")" .

  func =
    ABS
    | AND
    | ATN
    | COS
    | EXP
    | INT
    | LOG
    | NOT
    | OR
    | RND
    | SGN
    | SIN
    | SQR
    | TAN