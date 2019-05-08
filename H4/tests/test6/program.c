#include <stdio.h>
#include "CAT.h"

void CAT_execution (int userInput){
	CATData	d1;

	d1	= CAT_new(5);
  CAT_set(d1, 3);
	printf("H1: 	Value 1 = %ld\n", CAT_get(d1));

  return ;
}

int main (int argc, char *argv[]){
	CAT_execution(argc);

  printf("CAT invocations = %ld\n", CAT_invocations());
	return 0;
}
