
int x = 3;
int y = 4;

static int a = 8;
static int *b = &a;


int test1() {
  return x;
}

int test2() {
  return test1();
}
