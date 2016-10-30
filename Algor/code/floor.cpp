// horizon question

int minStep(int nFloor,int mStep) {
  int max = nFloor;
  int min = mStep;

  if (nFloor <= 0 || mStep <= 0 || mStep > max)
    return -1;

  while (mStep < min)
    mStep *= 2;
  return mStep;
}
