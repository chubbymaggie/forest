/*
 * First KLEE tutorial: testing a small function
 */


int getsign(int x) {
  if (x == 0)
     return 0;
  
  if (x < 0)
     return -1;
  else 
     return 1;
} 

int main() {
  int a;
  return getsign(a);
} 
