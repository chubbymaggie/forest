#include "../include/other.h"
#include "../include/string.h"



int strlen( char *str)
{
  const char *s;

  for (s = str; *s; ++s);
  return(s - str);
}



int strcmp(char* s1, char* s2)
{
    while(*s1 && (*s1==*s2))
        s1++,s2++;
    return *(unsigned char*)s1-*(unsigned char*)s2;
}
/*int strcmp(char *s1, char *s2)*/
/*{*/
    /*while((*s1 && *s2) && (*s1++ == *s2++));*/
    /*return *(--s1) - *(--s2);*/
/*}*/



/*int memcmp(const void* buf1,*/
		/*const void* buf2,*/
		/*size_t count)*/
/*{*/
	/*if(!count)*/
		/*return(0);*/

	/*while(--count && *(char*)buf1 == *(char*)buf2 ) {*/
		/*buf1 = (char*)buf1 + 1;*/
		/*buf2 = (char*)buf2 + 1;*/
	/*}*/

	/*return(*((unsigned char*)buf1) - *((unsigned char*)buf2));*/
/*}*/

int memcmp(const char *cs, const char *ct, size_t n)
{
  size_t i;   

  for (i = 0; i < n; i++, cs++, ct++)
  {
    if (*cs < *ct)
    {
      return -1;
    }
    else if (*cs > *ct)
    {
      return 1;
    }
    else
    {
      return 0;
    }
  }
} 

char *strchr(const char *s, int c) {
	while (*s != (char) c) {
		if (!*s++) {
			return 0;
		}
	}
	return (char *)s;
}


















