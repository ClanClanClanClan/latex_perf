/* LD_PRELOAD clock for the spike H.2 differential (docs/v27/spike/h2/diff/).
   gettimeofday(2) returns the readings of $LP_CLOCK ("SEC.USEC,SEC.USEC,...") in call
   order, the same readings the model receives as `clock SEC USEC` lines; when none is
   left it writes a message and exits with status 97 (the model is then Stuck; abort()
   is not used because qemu-user can hang on it), and appends "N SEC USEC" per call to
   $LP_CLOCK_LOG so the number of readings used can be compared with the model's.
   pdfTeX calls gettimeofday only in texmfmp.c get_seconds_and_micros (the one
   `bl gettimeofday@plt` of the aarch64 reference build). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>
#include <unistd.h>

static int calls;

int gettimeofday(struct timeval *restrict tv, void *restrict tz)
{
  const char *s = getenv("LP_CLOCK"), *lg = getenv("LP_CLOCK_LOG"), *p;
  long long sec;
  long usec;
  int i;
  (void) tz;
  if (!s) { fputs("lp-clock: LP_CLOCK is not set\n", stderr); _exit(97); }
  for (p = s, i = 0; i < calls; i++) {
    p = strchr(p, ',');
    if (!p) { fputs("lp-clock: no clock reading left\n", stderr); _exit(97); }
    p++;
  }
  if (sscanf(p, "%lld.%ld", &sec, &usec) != 2) { fputs("lp-clock: bad reading\n", stderr); _exit(97); }
  calls++;
  if (tv) { tv->tv_sec = (time_t) sec; tv->tv_usec = (suseconds_t) usec; }
  if (lg) {
    FILE *f = fopen(lg, "a");
    if (f) { fprintf(f, "%d %lld %ld\n", calls, sec, usec); fclose(f); }
  }
  return 0;
}
