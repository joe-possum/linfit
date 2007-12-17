static char *id __attribute__ ((__unused__)) = "@(#) ganesh:/mnt/gersemi/src/Linfit/linfit.c;"
                  "Friday November 24, 2006 (10:52);"
                  "Mark Orchard-Webb;"
                  "Compiled: "__DATE__ " (" __TIME__ ")" ;

/*
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

#include <limits.h>
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
	   "\t-h\tDisplay this informative help message\n", name);
  exit (1);
}

enum GRAPHS { NONE, GRAPH, RESIDUAL };

struct fit {
  double *indep, *dep, *error;
  int count, order;
  double *parameters, *errors;
};

int compare_magnitude (const void *aptr, const void *bptr)
{
  long double a = fabs (*(long double *)aptr);
  long double b = fabs (*(long double *)bptr);
  if (a > b) return 1;
  if (a < b) return -1;
  return 0;
}

int compare_double (const void *aptr, const void *bptr)
{
  double a = *(double *)aptr;
  double b = *(double *)bptr;
  if (a > b) return 1;
  if (a < b) return -1;
  return 0;
}

long double sum (long double *array, int N)
{
  int i;
  long double rv = 0;
  qsort (array, N, sizeof (long double), compare_magnitude);
  for (i = 0; i < N; i++)
    rv += array[i];
  return rv;
}

void print_matrix (long double **array, int N)
{
  int i, j;
  for (i = 0; i < N; i++) {
    printf ("[");
    for (j = 0; j < N; j++)
      printf ("%15g", (double) array[i][j]);
    printf ("]\n");
  }
}

long double determinant (long double **array, int N)
{
  long double rv = 1;
  int i, j, k;
  for (i = 0; i < N; i++) {
    if (array[i][i] == 0) {
      for (j = i; j < N; j++) {
	if (array[i][j]) {
	  for (k = 0; k < N; k++) {
	    long double tmp;
	    tmp = array[k][j];
	    array[k][j] = array[i][j];
	    array[i][j] = tmp;
	  }
	  rv = -rv;
#ifdef VERBOSE
	  printf ("swapped columns %d and %d; determinant = %g\n", i, j, rv);
	  print_matrix (array, N);
#endif
	  break;
	}
      }
      if (array[i][i] == 0) return 0;
    }
    rv *= array[i][i];
    for (j = i+1; j < N; j++) {
      long double tmp = array[j][i]/array[i][i];
#ifdef VERBOSE
      printf ("subtracting %g times row %d from row %d\n", tmp, i, j);
#endif
      for (k = i+1; k < N; k++) {
#ifdef VERBOSE
	printf ("%g ->", array[j][k]);
#endif
	array[j][k] -= array[i][k]*tmp;
#ifdef VERBOSE
	printf ("%g\n", array[j][k]);	
#endif
      }
    }
#ifdef VERBOSE
    printf ("determinant = %g\n", rv);
    print_matrix (array, N);
#endif
  }
  return rv;
}

int polyfit (struct fit *args)
{
  int i, j, p;
  const int N = args->order + 1;
  const int Nsq = N * N;
  long double **matrix;
  long double *W, *A;
  long double *sigma_pow_x, *sigma_y_pow_x;
  long double delta, inv_delta;	/* the ugly denominator */

  assert (W = malloc (args->count * sizeof (long double)));
  assert (A = malloc (args->count * sizeof (long double)));
  assert (sigma_pow_x = malloc (args->count * args->count * sizeof (long double)));
  assert (sigma_y_pow_x = malloc (args->count * sizeof (long double)));

  for (i = 0; i < args->count; i++) W[i] = 1 / (args->error[i] * args->error[i]);

  for (p = 1; p < Nsq; p++) {
    for (i = 0; i < args->count; i++) A[i] = W[i] * pow (args->indep[i], p);
    sigma_pow_x[p] = sum (A, args->count);
  }
  for (p = 0; p < N; p++) {
    for (i = 0; i < args->count; i++) A[i] = W[i] * pow (args->indep[i], p) * args->dep[i];
    sigma_y_pow_x[p] = sum (A, args->count);
  }

  sigma_pow_x[0] = sum (W, args->count);

  free (A);
  free (W);

  assert (matrix = malloc (N * sizeof (long double *)));
  for (i = 0; i < N; i++) {
    assert (matrix[i] = malloc (N * sizeof (long double)));
    for (j = 0; j < N; j++)
      matrix[i][j] = sigma_pow_x[i+j];
  }
  
  delta = determinant (matrix, N);
  inv_delta = 1 / delta;

  for (p = 0; p < N; p++) {
    for (i = 0; i < N; i++) {
      for (j = 0; j < N; j++)
	matrix[i][j] = (j == p) ? sigma_y_pow_x[i] : sigma_pow_x[i+j];
    }
    args->parameters[p] = inv_delta * determinant (matrix, N);
  }
  for (p = 0; p < N; p++) {
    for (i = 0; i < N-1; i++) {
      for (j = 0; j < N-1; j++) {
	int index = i+j+(i>=p)+(i>=p);
	matrix[i][j] = sigma_pow_x[index];
      }
    }
    args->errors[p] = sqrt(inv_delta * determinant (matrix, N-1));
  }
  for (i = 0; i < N; i++) free (matrix[i]);
  free (matrix);
  free (sigma_pow_x);
  free (sigma_y_pow_x);
  return 0;
}

double ChiSq (double *y, double *s, double *f, int N)
{
  int i;
  long double *dchi, delta, rv;
  assert (dchi = malloc (N * sizeof (long double)));
  for (i = 0; i < N; i++) {
    delta = (f[i] - y[i])/s[i];
    dchi[i] = delta * delta;
  }
  rv = sum (dchi, N);
  free (dchi);
  return rv;
}

double polynomial (const int N, const double *a, const double x)
{
  long double sigma[N+1];
  int i;
  long double p = 1;
  for (i = 0; i <= N; i++) {
    sigma[i] = a[i] * p;
    p *= x;
  }
  return sum (sigma, N+1);
}

void check_errors (struct fit *args)
{
  int i, p, ss, pp;
  double *fiddle, *f, chisq;
  assert (f = malloc (args->count * sizeof (double)));
  assert (fiddle = malloc ((args->order+1)*sizeof(double)));
  for (p = 0; p <= args->order; p++) {
    for (ss = 0; ss < 2; ss++) {
      for (pp = 0; pp <= args->order; pp++) {
	fiddle[pp] = args->parameters[pp];
	if (pp == p) fiddle[pp] += ((ss<<1)-1) * args->errors[pp];
      }
      for (i = 0; i < args->count; i++) {
	f[i] = polynomial (args->order, fiddle, args->indep[i]);
      }
      chisq = ChiSq (args->dep, args->indep, f, args->count);
      fprintf (stdout, "rChisq(a[%d]%csigma_a[%d]) = %.20g\n", p,ss?'-':'+',p,chisq / (args->count - (args->order+1)));
    }
  }
  free (fiddle);
}

/*
 * Use Newton's method to find the x such that erf(x) == prob
 */
#define MAXITER 32
int iterations[MAXITER];

double find_prob (double prob, double guess)
{
  double value, slope, dx, dy;
  unsigned int i;
  double *vptr, *pptr;
  vptr = &value;
  pptr = &prob;
  if (prob == 0) return 0;
  for (i = 1;; i++) {
    value = erf(guess);
    if (*vptr == *pptr) break;
    dy = value - prob;
    slope = 2/sqrt(M_PI)*exp (-guess*guess);
    dx = dy / slope;
    guess -= dx;
    if (i == MAXITER) break;
  }
  iterations[i-1]++;
  return guess;
}

double get_gaussian (double mu, double sigma)
{
  return sqrt(2) * sigma * find_prob (rand() / (double) INT_MAX, 0.5) *
    ((rand() & 1) ? 1 : -1) + mu;
}

double gaussian (double x, double mu, double sigma)
{
  double z = (x - mu) / sigma;
  return exp (-0.5 * z * z) / (sqrt(2*M_PI) * sigma);
}

int gen_stat (int order, double xm)
{
  const int npts = 100;
  const int iterations = 1000;
  const double sigma = 1;
  int counters[order+1];
  double sigmas[order+1];
  double x[npts], y[npts], e[npts];
  double true[order+1], parameters[order+1], errors[order+1];
  double saveparams[order+1][iterations];
  struct fit fit;
  int i, j, k;
  double delta, maxdelta;
  int histogram[100];
  double chisq;
  int nzc;

  srand (time(NULL));
  
  fit.indep = x;
  fit.dep = y;
  fit.error = e;
  fit.order = order;
  fit.count = npts;
  fit.parameters = parameters;
  fit.errors = errors;
  for (k = 0; k <= order; k++) {
    true[k] = rand() / (double) INT_MAX;
    counters[k] = 0;
    sigmas[k] = 0;
  }
  for (j = 0; j < npts; j++) x[j] = (xm*j)/npts;
  for (i = 0; i < iterations; i++) {
    for (j = 0; j < npts; j++) {
      y[j] = get_gaussian (polynomial(order, true, x[j]), sigma);
      e[j] = sigma;
    }
    polyfit( &fit);
    for (k = 0; k <= order; k++) if (fabs (parameters[k] - true[k]) < errors[k]) counters[k]++;
    for (k = 0; k <= order; k++) sigmas[k] += (parameters[k] - true[k])*(parameters[k] - true[k]);
    for (k = 0; k <= order; k++) saveparams[k][i] = parameters[k] - true[k];
  }
  printf ("%g ", xm);
  for (k = 0; k <= order; k++) printf ("%.20g ", sigmas[k]/iterations);
  for (k = 0; k <= order; k++) {
    for (i = 0; i < 100; i++) histogram[i] = 0;
    qsort (saveparams[k],iterations,sizeof(double),compare_double);
    maxdelta = 0;
    for (i = 1; i < iterations; i++) {
      delta = saveparams[k][i] - saveparams[k][i-1];
      if (delta > maxdelta) {
	maxdelta = delta;
      }
    }
    delta = saveparams[k][i-1] - saveparams[k][0];
    for (i = 0; i < iterations; i++) histogram[(int)((saveparams[k][i] - saveparams[k][0])/maxdelta)]++;
    chisq = 0;
    nzc = 0;
    for (i = 0; (i < 100) && histogram[i]; i++) {
      nzc++;
      chisq += pow (iterations * maxdelta * gaussian((i+.5)*maxdelta+saveparams[k][0],0,sqrt(sigmas[k]/iterations)) - histogram[i], 2) / histogram[i];
    }
    printf ("%.20g ", chisq / (nzc - 1));
  }
  printf ("\n");
  return 0;
}
  
int polyfit_we (struct fit *args)
{
  double *sigma_sq, dparam;
  int i, p;
  struct fit vary;
  polyfit (args);
  assert (sigma_sq = malloc ((args->order+1)*sizeof(double)));
  vary.indep = args->indep;
  assert (vary.dep = malloc (args->count * sizeof (double)));
  vary.error = args->error;
  vary.order = args->order;
  vary.count = args->count;
  assert (vary.parameters = malloc ((args->order+1)*sizeof(double)));
  assert (vary.errors = malloc ((args->order+1)*sizeof(double)));
  for (p = 0; p <= args->order; p++) sigma_sq[p] = 0;
  for (i = 0; i < args->count; i++) vary.dep[i] = args->dep[i];
  for (i = 0; i < args->count; i++) {
    vary.dep[i] = args->dep[i] + args->error[i];
    polyfit (&vary);
    vary.dep[i] = args->dep[i];
    for (p = 0; p <= args->order; p++) {
      dparam = vary.parameters[p] - args->parameters[p];
      sigma_sq[p] += dparam*dparam;
    }
  }
  for (p = 0; p <= args->order; p++) args->errors[p] = sqrt(sigma_sq[p]);
  for (p = 0; p <= args->order; p++) printf ("sigma_a[%d]: %.20g vs %.20g\n", p, args->errors[p], vary.errors[p]);
  free (vary.parameters);
  free (vary.dep);
  free (sigma_sq);
  return 0;
}

struct data {
  int xcol,			/*!< column number of independent data (1 based) */
    ycol,			/*!< column number of dependent data (1 based) */
    ecol;			/*!< column number of error on dependent data (1 based, use expression if 0) */
  char *expr;			/*!< expression for calulating error on dependent variable */
  int count;			/*!< count of triplets parsed */
  double *x, *y, *e;		/*!< data triplets */
};

int parse_data (FILE *in, struct data *data)
{
  const int MAXLEN = 1024;
  char line[1024];
  const char *whitespace = " \t\n\r";
  char *ptr, *xptr, *yptr, *eptr;
  int i, column;
  double x, y, e;
  
  data->count = 0;
  FILE *xfd, *yfd, *efd;
  assert(xfd = tmpfile());
  assert(yfd = tmpfile());
  if (data->ecol) assert (efd = tmpfile ());
  while (fgets (line, MAXLEN, in)) { /* read a whole line into buffer */
    for (i = 0; i < strlen (comments); i++) { /* Strip out comments */
      ptr = strchr (line, comments[i]);
      if (ptr) *ptr = 0;	/* if found, terminate the string at this character */
    }
    column = 0;
    xptr = yptr = eptr = NULL;
    for (ptr = strtok (line, whitespace); ptr; ptr = strtok (NULL, whitespace)) {
      column++;
      if (column == data->xcol) xptr = ptr;
      if (column == data->ycol) yptr = ptr;
      if (column == data->ecol) eptr = ptr;
      if (xptr && yptr && (!data->ecol || eptr)
	  && (sscanf (xptr, "%lg", &x) == 1)
	  && (sscanf (yptr, "%lg", &y) == 1)
	  && (!data->ecol || (sscanf (eptr, "%lg", &e) == 1))) {
	fwrite (&x, sizeof(double), 1, xfd);
	fwrite (&y, sizeof(double), 1, yfd);
	if (data->ecol) fwrite (&e, sizeof(double), 1, efd);
	data->count++;
      }
    }
  }
  assert (data->x = calloc(data->count, sizeof (double)));
  assert (data->y = calloc(data->count, sizeof (double)));
  assert (data->e = calloc(data->count, sizeof (double)));
  rewind (xfd);
  fread (data->x, sizeof (double), data->count, xfd);
  fclose (xfd);
  rewind (yfd);
  fread (data->y, sizeof (double), data->count, yfd);
  fclose (yfd);
  if (data->ecol) {
    rewind (efd);
    fread (data->e, sizeof (double), data->count, efd);
    fclose (efd);
  }
  fprintf (stderr, "read %d triplets\n", data->count);
  return 0;
}

int main (int argc, char **argv)
{
  int i, j;
  double *f;			/*!< Storage for the function values */
  double chisq;
  int ch;
  FILE *in, *out, *awk;
  time_t tm;
  enum GRAPHS graph = NONE;
  char *filename = NULL;
  struct fit args;
  struct data data = {
    .xcol = 1,
    .ycol = 2,
    .ecol = 3,
    .expr = NULL
  };
  
  time (&tm);
  in = stdin;
  out = stdout;
  awk = NULL;
  args.order = 1;
  
  while ((ch = getopt (argc, argv, "a:n:dhrg")) != EOF)
    switch (ch) {
    case 'h':
      usage (argv[0]);
    case 'd':
      debug++;
      break;
    case 'g':
      graph = GRAPH;
      break;
    case 'r':
      graph = RESIDUAL;
      break;
    case 'a':
      fprintf (stderr, "Calibration conversion will be written to %s\n", optarg);
      awk = fopen (optarg, "w");
      if (awk == NULL)
	die ("Can't open %s for write: %s", strerror(errno));
      break;
    case 'n':
      if (sscanf (optarg, "%d", &args.order) != 1) die ("could not parse order of polynomial, you said \"-n %s\"\n", optarg);
      fprintf (stderr, "fitting to polynomial of order %d\n", args.order);
#ifdef STATS
      {
	int i, j;
	for (j = 0; j < 10; j++) for (i = 1; i < 10; i++) gen_stat (args.order, (double) i);
      }
      return 0;
#endif
      break;
    default:
      die ("Unknown switch provided '%c'\n", optopt);
    }
  filename = "-";		/* used later in gnuplot output */
  if (optind < argc) {
    filename = argv[optind];
    in = fopen (filename, "r");
    if (in == NULL)
      die ("Unable to open %s for read: %s\n", filename, strerror(errno));
  }
  parse_data (in, &data);
  args.indep = data.x;
  args.dep = data.y;
  args.error = data.e;
  args.count = data.count;
  assert (args.parameters = malloc ((args.order + 1) * sizeof (double)));
  assert (args.errors = malloc ((args.order + 1) * sizeof (double)));
  polyfit (&args);
  fprintf (out, "y(x) = a");
  for (i = 1; i <= args.order; i++) {
    fprintf (out, " + %c * x", 'a'+i);
    for (j = 1; j < i; j++) fprintf (out, "*x");
  }
  fprintf (out, "\n");
  
  for (i = 0; i <= args.order; i++) {
    fprintf (out, "%c = %.20g\n", 'a'+i, args.parameters[i]);
    fprintf (out, "sigma_%c = %.20g\n", 'a'+i, args.errors[i]);
  }
  
  chisq = 0;
  assert (f = malloc (data.count * sizeof (double)));
  for (i = 0; i < data.count; i++) {
    f[i] = polynomial (args.order, args.parameters, data.x[i]);
  }
  chisq = ChiSq (data.y, data.e, f, data.count);
  fprintf (out, "rChisq = %.20g\n", chisq / (data.count - (args.order+1)));
  if (in == stdin) {
    data.xcol = 1;
    data.ycol = 2;
    data.ecol = 3;
  }
  switch (graph) {
  case GRAPH:
    fprintf (out, "plot '%s' using ($%d):($%d):($%d) with error, y(x) with line\n", filename, data.xcol, data.ycol, data.ecol);
    break;
  case RESIDUAL:
    fprintf (out, "plot '%s' using ($%d):($%d-y($%d)):($%d) with error\n", filename, data.xcol, data.ycol, data.xcol, data.ecol);
    break;
  case NONE:
    break;
  }
  if (graph && (in == stdin)) {
    for (i = 0; i < data.count; i++)
      fprintf (out, "%.20g \t%.20g \t%.20g\n", data.x[i], data.y[i], data.e[i]);
  }
  fclose (out);
  return 0;
}
