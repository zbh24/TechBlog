module Main where
       sorted [] = True
       sorted [x] = True
       sorted (x:y:l) = if x <= y then sorted (y:l) else False

       ins::Integer->[Integer]->[Integer]
       ins x [] = [x]
       ins x (y:l) = if x>y then y:(ins x l) else x:y:l

       insort [] = []
       insort (x:l) = ins x (insort l)

       split [] = ([],[])
       split [x] = ([x],[])
       split (x:y:l) = let (a,b) = split l
                       in (x:a,y:b)

       merge [] l = l
       merge l [] = l
       merge (x:l1) (y:l2) = if x <= y then x:(merge l1 (y:l2)) else y:(merge (x:l1) l2)


       msort [] = []
       msort [x] = [x]
       msort l = let (a,b) = split l
                 in merge (msort a) (msort b)
       

       partion [] n = ([],[])
       partion [x] n = if x<=n then ([x],[]) else ([],[x])
       partion (x:l) n = let  (smalls, bigs) = partion l n
       	                 in 
			 if x <= n 
			 then (x:smalls,bigs) 
			 else (smalls,x:bigs) 

       append [x] [] = [x]
       append [] l = l
       append (x:l1) l2 = x : (append l1 l2)

       qsort [] = []
       qsort [x] = [x]
       qsort (x:l)  = let  (a,b) = partion l x
                      in append (qsort a) (x:(qsort b))


		 