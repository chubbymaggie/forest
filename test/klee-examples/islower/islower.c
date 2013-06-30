/*
 * First KLEE tutorial: testing a small function
 */


int myislower(int x) {
  if (x >= 'a' && x <= 'z')
    return 1;
  else return 0;
}

int main() {
  char c;
  return myislower(c);
}
