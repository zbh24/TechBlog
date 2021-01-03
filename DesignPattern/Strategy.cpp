class Opertion {
  int a;
  int b;
  virtual int GetResutlt();
}

class AddOpertion : Opertion {
  int GetResult() {
    return a + b;
  }
}

class MinOpertion : Opertion {
  int GetResult() {
    return a - b;
  }
}

class ChenOpertion : Opertion {
  int GetResult() {
    return a * b;
  }
}

class ChuOpertion : Opertion {
  int GetResult() {
    return a / b;
  }
}

class OpertionContext {
  Opertion local;
  OpertionContext(char c) {
    switch (c) {
      case '+':
        local = new AddOpertion();
        break;
      case '-':
        local = new MinOpertion();
        break;
    }
  }

  int GetResult() {
    return local.GetResult();
  }
}

// clinit
int main() {
  OpertionContext temp = new OpertionContext(GetInput());
  return temp.GetResult();
}
