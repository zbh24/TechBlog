all:	
	gcc --shared -fpic test.cpp -o libtest.so

clean:
	rm *.so elf_file

elf:	all
	readelf -a -W libtest.so > elf_file
dump:
	objdump -s --start-address=0x00000000000004b8 libtest.so | more
