#define HELP_OPTION_DESCRIPTION \
  _("      --help     display this help and exit\n")
#define VERSION_OPTION_DESCRIPTION \
  _("      --version  output version information and exit\n")

#define PACKAGE_BUGREPORT "pabloga@teisa.unican.es"

static inline void
emit_bug_reporting_address (void)
{
  /* TRANSLATORS: The placeholder indicates the bug-reporting address
     for this package.  Please add _another line_ saying
     "Report translation bugs to <...>\n" with the address for translation
     bugs (typically your translation team's web or email address).  */
  printf (_("\nReport bugs to <%s>.\n"), PACKAGE_BUGREPORT);
}

