from heapq import *
from random import shuffle

data = range(10)

shuffle(data)

heap = []

for n in data:
	heappush(heap,n)


print heap

heappush(heap,0.5)

print heap

heappop(heap)

print heap

a = [45,32,44,1]

heapify(a)

print a


