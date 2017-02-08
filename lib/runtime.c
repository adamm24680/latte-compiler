#include "stdio.h"
#include "stdlib.h"
#include "string.h"

#define BUFSIZE 1000

void printInt(int a) {
  printf("%d\n",a);
}
void printString(char* a) {
  printf("%d\n",a);
}
void error() {
  printf("runtime error\n");
  abort();
}
int readInt() {
  int k;
  int num = scanf("%d", &k);
  if (num ==1)
      return k;
  else {
      printf("error reading int\n");
      error();
  }
  return k;
}
char* readString() {
  static char k[BUFSIZE];
  fgets(k, BUFSIZE, stdin);
  size_t len = strlen(k);
  char* new = malloc(len+1);
  return strcpy(new, k);
}
