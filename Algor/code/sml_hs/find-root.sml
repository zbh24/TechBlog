fun findroot (a,x,acc) =
    let val nextx = (a/x + x) / 2.0
    in if abs (x-nextx) < acc * x
        then nextx
	else findroot (a,nextx,acc)
    end;
 
fun sqroot a = findroot (a,1.0,1.0E~10);

sqroot 2.0;


fun fs (a,oldx,highx,lowx,acc) =
    let val x = (highx + lowx) / 2.0; 
    in if abs (x-oldx) < acc * oldx
    then x
    else if x * x > a
         then fs(a,x,x,lowx,acc)
	 else fs(a,x,highx,x,acc)
   end;

fun sqr a = fs (a,a,a,1.0,1.0E~10);

sqr 2.0;

fun sqr1 a =
    let val acc = 1.0E~10;
    fun fs (a,oldx,highx,lowx,acc) =
    	let val x = (highx + lowx) / 2.0; 
    	in if abs (x-oldx) < acc * x
    	then x
    	else if x * x > a 
             then fs(a,x,x,lowx,acc)
	     else fs(a,x,highx,x,acc)
	end
    in fs (a,a,a,1.0,acc) end;

sqr1 2.0;
