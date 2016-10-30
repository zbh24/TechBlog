#include <stdio.h>
#include <stdlib.h>

int main(void) 
{
  int c2 = 2;
  int c1 = 2;
  int c0 = 2;
  int b;
  for(b = 3; ; b++)
    {
      printf("%d %d %d [%d]\n",c2,c1,c0,b);
      if (0 < c0)
	c0--;
      else if (0 < c1)
	{
	  c1--;
	  c0 = b;
	}
      else if (0 < c2)
	{
	  c2--;
	  c0 = c1 = b;
	}
      else break;
    }
  printf("I am finished with b=%d\n",b);
  return EXIT_SUCCESS;
}
