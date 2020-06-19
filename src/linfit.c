static char *id __attribute__ ((__unused__)) 
  = "@(#) ganesh:URL: http://www.ugrad.physics.mcgill.ca/SVN/linfit/src/linfit.c;"
    "Tuesday February  5, 2008 (15:33) (Revision: 1 before commit);"
    "Mark Orchard-Webb;"
    "Compiled: "__DATE__ " (" __TIME__ ")" ;

/*
 * Tuesday February  5, 2008 (15:33) (Revision: 1 before commit)
 * =============================================================
 * 
 * Removed default output of rChisq test
 * 
 * Friday November 24, 2006 (10:52)
 * ================================
 * 
 * Rewritten with linfit as a function.  Leaning towards making an external function for a library.
 * 
 * Monday February  3, 2003 (18:25)
 * ================================
 * 
 * A brilliant idea comes to me
 *   New switches:
 *     -g : generate a graph
 *     -r : generate a residual graph
 * 
 * Monday January 17, 2000 (09:40)
 * =================================
 * 
 * No change, just relocation
 * 
 * Wednesday January 21, 1998
 * ==========================
 *
 * Original implimentation, a replacement of the awk script,
 * which was itself a replacement for a QuickBASIC program
 *
 */

/*
 * Linfit a linear regression program
 *
 * Algorithm stolen from Bevington ... no algorithmic comments
 *
 */

#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <errno.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <die.h>
#include <assert.h>

const char *comments = "#%!;";
int debug = 0;

void usage (const char *name)
{
  fprintf (stderr,
	   "Usage:\t%s [ -h ] [ datafile ]\n"
	   "\tPerforms linear regressions upon datafile, or stdin.  Assumes\n"
	   "\ttriplets of {x, y, sigma}, one per line.\n\n"
	   "\t-a filename\tWrite an awk calibration script to filename\n"
	   "\t-d Turn on debugging output\n"
	   "\t-g\tWrite a gnuplot script showing graph of fit to stdout\n"
	   "\t-r\tWrite a gnuplot script showing residual to stdout\n"
	   "\t-s suffix\tAdd suffix to variables\n"
	   "\t-p title\tSet title for data points\n"
	   "\t-l title\tSet title for best-fit line\n"
	   "\t-h\tDisplay this informative help message\n", name);
  exit (1);
}

int resize (double **x, double **y, double **s, int *size)
{
  if (*size == 0) {
    *x = *y = *s = NULL;
    *size = 16;
  }
  *size <<= 1;			/* double the size */
  *x = realloc (*x, *size * sizeof (double));
  *y = realloc (*y, *size * sizeof (double));
  *s = realloc (*s, *size * sizeof (double));
  if (!*x || !*y || !*s)
    die ("Problem allocating arrays for %d lines of data", *size);
  if (debug) fprintf (stderr, "Arrays resized to %d rows\n", *size);
  return 0;
}

enum GRAPHS { NONE, GRAPH, RESIDUAL };

struct fit {
  double *indep, *dep, *error;
  int count;
  double slope, e_slope, offset, e_offset;
};

int compare_magnitude (const void *aptr, const void *bptr)
{
  double a = fabs (*(double *)aptr);
  double b = fabs (*(double *)bptr);
  if (a > b) return 1;
  if (a < b) return -1;
  return 0;
}

double sum (double *array, int N)
{
  int i;
  double rv = 0;
  qsort (array, N, sizeof (double), compare_magnitude);
  for (i = 0; i < N; i++)
    rv += array[i];
  return rv;
}

int linfit (struct fit *args)
{
  int i;
  double *W, *A;
  double 
    w_sigma_x = 0,		/* the running summations */
    w_sigma_x2 = 0,		/* all nicely zeroed */
    w_sigma_y = 0,
    w_sigma_xy = 0,
    w_sigma = 0;
  double delta, inv_delta;	/* the ugly denominator */
  double a, sigma_a, b, sigma_b; /* the parameters */

  assert ((W = malloc (args->count * sizeof (double))));
  assert ((A = malloc (args->count * sizeof (double))));

  for (i = 0; i < args->count; i++) W[i] = 1 / (args->error[i] * args->error[i]);

  for (i = 0; i < args->count; i++) A[i] = W[i] * args->indep[i];
  w_sigma_x = sum (A, args->count);

  for (i = 0; i < args->count; i++) A[i] = W[i] * args->indep[i] * args->indep[i];
  w_sigma_x2 = sum (A, args->count);

  for (i = 0; i < args->count; i++) A[i] = W[i] * args->dep[i];
  w_sigma_y += sum (A, args->count);

  for (i = 0; i < args->count; i++) A[i] = W[i] * args->indep[i] * args->dep[i];
  w_sigma_xy = sum (A, args->count);

  w_sigma = sum (W, args->count);

  free (A);
  free (W);
  
  delta = w_sigma * w_sigma_x2 - w_sigma_x * w_sigma_x;
  inv_delta = 1 / delta;
  
  a = inv_delta * (w_sigma_x2 * w_sigma_y - w_sigma_x * w_sigma_xy);
  sigma_a =  inv_delta * w_sigma_x2;
  b = inv_delta * (w_sigma * w_sigma_xy - w_sigma_x * w_sigma_y);
  sigma_b = inv_delta * w_sigma;
  args->offset = a;
  args->e_offset = sqrt(sigma_a);
  args->slope = b;
  args->e_slope = sqrt(sigma_b);
  return 0;
}

double ChiSq (double *y, double *s, double *f, int N)
{
  int i;
  double *dchi, delta, rv;
  assert ((dchi = malloc (N * sizeof (double))));
  for (i = 0; i < N; i++) {
    delta = (f[i] - y[i])/s[i];
    dchi[i] = delta * delta;
  }
  rv = sum (dchi, N);
  free (dchi);
  return rv;
}

int main (int argc, char **argv)
{
  char line [256];		/* used to buffer a whole line of input */
  char *ptr;
  int i;
  double *x, *y, *s;		/* input variables */
  double *f;			/*!< Storage for the function values */
  int line_count = 0, rc;	/* used for debugging bad data input */
  int data_count = 0;
  int data_size = 0;		/* array size */
  double chisq;
  int ch;
  int test_errors = 0;		/*!< Testing of ChiSq response to change of parameters  */
  FILE *in, *out, *awk;
  time_t tm;
  enum GRAPHS graph = NONE;
  char *filename = NULL, *suffix = "", *points = "", *lines = "";
  struct fit args;
  
  time (&tm);
  in = stdin;
  out = stdout;
  awk = NULL;

  while ((ch = getopt (argc, argv, "a:dhrgs:p:l:")) != EOF)
    switch (ch) {
    case 'h':
      usage (argv[0]);
    case 'd':
      debug++;
      break;
    case 'g':
      graph = GRAPH;
      break;
    case 's':
      suffix = strdup(optarg);
      break;
    case 'r':
      graph = RESIDUAL;
      break;
    case 'p':
      points = strdup(optarg);
      break;
    case 'l':
      lines = strdup(optarg);
      break;
    case 'a':
      fprintf (stderr, "Calibration conversion will be written to %s\n", optarg);
      awk = fopen (optarg, "w");
      if (awk == NULL)
	die ("Can't open %s for write: %s", strerror(errno));
      break;
    default:
      die ("Unknown switch provided '%c'\n", optopt);
    }
  if (optind < argc) {
    filename = argv[optind];
    in = fopen (filename, "r");
    if (in == NULL)
      die ("Unable to open %s for read: %s\n", filename, strerror(errno));
  } else {
    if (graph) {
      die ("Can't generate a graph with data from stdin!");
    }
  }
  data_count = 0;
  data_size = 0;
  while (fgets (line, 256, in)) { /* read a whole line into buffer */
    if (data_count == data_size) {
	resize (&x, &y, &s, &data_size); /* this will die if there is an error */
    }
    line_count++;			/* increment line counter */
    for (i = 0; i < strlen (comments); i++) { /* Strip out comments */
      ptr = strchr (line, comments[i]);
      if (ptr) *ptr = 0;	/* if found, terminate the string at this character */
    }
    rc = sscanf (line, "%lf %lf %lf", /* attempt to parse variables */
		 &x[data_count], &y[data_count], &s[data_count]); 
    if ((rc > 0) && (rc != 3)) { /* if didn't find all three issue a warning */
      fprintf (stderr, "Less than three floats on line %i:\n\"%s\"\n", line_count, line);
    } else if (s[data_count] == 0) {
      fprintf (stderr, "Ignoring line %d:%s ... uncertainty can't be zero!\n",
	       line_count, line);
    } else if (rc == 3) {
      if (debug) fprintf (stderr, "data -> %g %g %g\n",
			  x[data_count], y[data_count], s[data_count]);
      data_count++;
    }
  }
  args.indep = x;
  args.dep = y;
  args.error = s;
  args.count = data_count;
  linfit (&args);
  fprintf (out, "a%s = %.20g\n", suffix,args.offset);
  fprintf (out, "sigma_a%s = %.20g\n", suffix,args.e_offset);
  fprintf (out, "b%s = %.20g\n", suffix,args.slope);
  fprintf (out, "sigma_b%s = %.20g\n", suffix,args.e_slope);
  fprintf (out, "y%s(x) = a%s + b%s * x\n",suffix,suffix,suffix);
  chisq = 0;
  assert ((f = malloc (data_count * sizeof (double))));
  for (i = 0; i < data_count; i++) {
    f[i] = args.offset + args.slope * x[i];
  }
  chisq = ChiSq (y, s, f, data_count);
  fprintf (out, "rChisq%s = %.20g\n", suffix,chisq / (data_count - 2));
  if (test_errors == 1) {
    for (i = 0; i < data_count; i++) {
      f[i] = (args.offset+args.e_offset) + args.slope * x[i];
    }
    chisq = ChiSq (y, s, f, data_count);
    fprintf (out, "rChisq(a+sigma_a) = %.20g\n", chisq / (data_count - 2));
    for (i = 0; i < data_count; i++) {
      f[i] = (args.offset-args.e_offset) + args.slope * x[i];
    }
    chisq = ChiSq (y, s, f, data_count);
    fprintf (out, "rChisq(a-sigma_a) = %.20g\n", chisq / (data_count - 2));
    for (i = 0; i < data_count; i++) {
      f[i] = args.offset + (args.slope+args.e_slope) * x[i];
    }
    chisq = ChiSq (y, s, f, data_count);
    fprintf (out, "rChisq(b+sigma_b) = %.20g\n", chisq / (data_count - 2));
    for (i = 0; i < data_count; i++) {
      f[i] = args.offset + (args.slope-args.e_slope) * x[i];
    }
    chisq = ChiSq (y, s, f, data_count);
    fprintf (out, "rChisq(b-sigma_b) = %.20g\n", chisq / (data_count - 2));
  }
  
  if (awk) {
    fprintf (awk, "# Script generated by %s on %s", argv[0], ctime (&tm));
    fprintf (awk,
	     "BEGIN {\n"
	     "  a = %.20g\n"
	     "  b = %.20g\n"
	     "}\n\n", args.offset, args.slope);
    fprintf (awk,
	     "{\n"
	     "  $1 = a + b * $1;\n"
	     "  print $0;\n"
	     "}\n");
    fclose (awk);
  }
  switch (graph) {
  case GRAPH:
    fprintf (out, "plot '%s' using ($1):($2):($3) with error title '%s', y%s(x) with line title '%s'\n", filename,points,suffix,lines);
    break;
  case RESIDUAL:
    fprintf (out, "plot '%s' using ($1):($2-y%s($1)):($3) with error\n", filename,suffix);
    break;
  case NONE:
    break;
  }
  return 0;
}
