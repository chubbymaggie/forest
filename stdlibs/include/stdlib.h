#define EXIT_SUCCESS 0
#define EXIT_FAILURE 1

#define _(msgid) gettext(msgid)


const char* gettext(const char* msgid){
	return msgid;
}

void exit(int a);

#define initialize_main(ac, av)



int atexit(void (*function)(void));




