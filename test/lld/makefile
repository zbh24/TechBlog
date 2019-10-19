g++ -fPIC -c add.cpp -o add
g++ -shared -o libadd.so add.o
#g++ -o main main.cpp -L. -ladd
#export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/Users/zhangbichao/techo/code/TechBlog/test/lld
#g++ -o main main.cpp -L. -ladd -Wl,-rpath=./
g++ -o main main.cpp -L. -ladd -Wl,-rpath,./
