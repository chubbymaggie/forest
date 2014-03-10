/*
 * =====================================================================================
 * /
 * |     Filename:  extra.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  12/20/2013 04:56:04 PM
 * |     Revision:  none
 * |     Compiler:  gcc
 * `-. .--------------------
 *    Y
 *    ,,  ,---,
 *   (_,\/_\_/_\     Author:   Pablo González de Aledo (), pablo.aledo@gmail.com
 *     \.\_/_\_/>    Company:  Universidad de Cantabria
 *     '-'   '-'
 * =====================================================================================
 */

#define MB_LEN_MAX 6

#define R(a,b) ((uint32_t)((a==0x80 ? 0x40-b : -a) << 23))

#define C(x) ( x<2 ? -1 : ( R(0x80,0xc0) | x ) )
#define D(x) C((x+16))
#define E(x) ( ( x==0 ? R(0xa0,0xc0) : \
                 x==0xd ? R(0x80,0xa0) : \
                 R(0x80,0xc0) ) \
             | ( R(0x80,0xc0) >> 6 ) \
             | x )
#define F(x) ( ( x>=5 ? 0 : \
                 x==0 ? R(0x90,0xc0) : \
                 x==4 ? R(0x80,0xa0) : \
                 R(0x80,0xc0) ) \
             | ( R(0x80,0xc0) >> 6 ) \
             | ( R(0x80,0xc0) >> 12 ) \
             | x )

const uint32_t bittab[] = {
	              C(0x2),C(0x3),C(0x4),C(0x5),C(0x6),C(0x7),
	C(0x8),C(0x9),C(0xa),C(0xb),C(0xc),C(0xd),C(0xe),C(0xf),
	D(0x0),D(0x1),D(0x2),D(0x3),D(0x4),D(0x5),D(0x6),D(0x7),
	D(0x8),D(0x9),D(0xa),D(0xb),D(0xc),D(0xd),D(0xe),D(0xf),
	E(0x0),E(0x1),E(0x2),E(0x3),E(0x4),E(0x5),E(0x6),E(0x7),
	E(0x8),E(0x9),E(0xa),E(0xb),E(0xc),E(0xd),E(0xe),E(0xf),
	F(0x0),F(0x1),F(0x2),F(0x3),F(0x4)
};

#define int32_t int

int errno;

#define EILSEQ               0
#define EDOM                 1
#define ERANGE               2
#define ENOTTY               3
#define EACCES               4
#define EPERM                5
#define ENOENT               6
#define ESRCH                7
#define EEXIST               8
#define EOVERFLOW            9
#define ENOSPC               10
#define ENOMEM               11
#define EBUSY                12
#define EINTR                13
#define EAGAIN               14
#define ESPIPE               15
#define EXDEV                16
#define EROFS                17
#define ENOTEMPTY            18
#define ECONNRESET           19
#define ETIMEDOUT            20
#define ECONNREFUSED         21
#define EHOSTDOWN            22
#define EHOSTUNREACH         23
#define EADDRINUSE           24
#define EPIPE                25
#define EIO                  26
#define ENXIO                27
#define ENOTBLK              28
#define ENODEV               29
#define ENOTDIR              30
#define EISDIR               31
#define ETXTBSY              32
#define ENOEXEC              33
#define EINVAL               34
#define E2BIG                35
#define ELOOP                36
#define ENAMETOOLONG         37
#define ENFILE               38
#define EMFILE               39
#define EBADF                40
#define ECHILD               41
#define EFAULT               42
#define EFBIG                43
#define EMLINK               44
#define ENOLCK               45
#define EDEADLK              46
#define ENOTRECOVERABLE      47
#define EOWNERDEAD           48
#define ECANCELED            49
#define ENOSYS               50
#define ENOMSG               51
#define EIDRM                52
#define ENOSTR               53
#define ENODATA              54
#define ETIME                55
#define ENOSR                56
#define ENOLINK              57
#define EPROTO               58
#define EBADMSG              59
#define EBADFD               60
#define ENOTSOCK             61
#define EDESTADDRREQ         62
#define EMSGSIZE             63
#define EPROTOTYPE           64
#define ENOPROTOOPT          65
#define EPROTONOSUPPORT      66
#define ESOCKTNOSUPPORT      67
#define ENOTSUP              68
#define EPFNOSUPPORT         69
#define EAFNOSUPPORT         70
#define EADDRNOTAVAIL        71
#define ENETDOWN             72
#define ENETUNREACH          73
#define ENETRESET            74
#define ECONNABORTED         75
#define ENOBUFS              76
#define EISCONN              77
#define ENOTCONN             78
#define ESHUTDOWN            79
#define EALREADY             80
#define EINPROGRESS          81
#define ESTALE               82
#define EREMOTEIO            83
#define EDQUOT               84
#define ENOMEDIUM            85
#define EMEDIUMTYPE          86


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




char *strcpy(char *dest, const char *src)
{
	const unsigned char *s = src;
	unsigned char *d = dest;
	while ((*d++ = *s++));
	return dest;
}



