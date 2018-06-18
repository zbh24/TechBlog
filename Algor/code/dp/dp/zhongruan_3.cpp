#include <stdio.h>
#include <string.h>
#include <math.h>
#include <stdlib.h>

#define NUM 100

int input[NUM+3][NUM+3];
int dij[NUM+3][NUM+3];

int main() {
  
  memset(input,0,sizeof(dij));
  for(int i = 1;i <= NUM; i++)
   for(int j = 1;j <= NUM; j++) {
     dij[i][j] = (dij[i-1][j]>dij[i][j-1]?dij[i-1][j]:dij[i][j-1]) + input[i][j];
   }
   return dij[NUM][NUM];
}


