void
parse_long_options (int argc,
		    char **argv,
		    const char *command_name,
		    const char *package,
		    const char *version,
		    void (*usage_func) (int),
		    /* const char *author1, ...*/ ...)
{
	int c;
	int saved_opterr;

	saved_opterr = opterr;

	/* Don't print an error message for unrecognized options.  */
	opterr = 0;

	if (argc == 2
			&& (c = getopt_long (argc, argv, "+", long_options, NULL)) != -1)
	{
		switch (c)
		{
			case 'h':
				(*usage_func) (EXIT_SUCCESS);

			case 'v':
				{
					va_list authors;
					va_start (authors, usage_func);
					version_etc_va (stdout, command_name, package, version, authors);
					exit (0);
				}

			default:
				/* Don't process any other long-named options.  */
				break;
		}
	}

	/* Restore previous value.  */
	opterr = saved_opterr;

	/* Reset this to zero so that getopt internals get initialized from
	   the probably-new parameters when/if getopt is called later.  */
	optind = 0;
}
