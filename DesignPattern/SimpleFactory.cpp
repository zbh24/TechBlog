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

class Factory {
  static Opertion GetOpertion(char c) {
    Opertion x = null;
    switch (c) {
      case '+':
        x = new AddOpertion();
        return x;
        break;
      case '-':
        x = new MinOpertion();
        return x;
        break;
    }
    return x;
  }
}

// clinit
int main() {
  Opertion temp = Factory.GetOpertion(GetInput());
  return temp.GetResult();
}
