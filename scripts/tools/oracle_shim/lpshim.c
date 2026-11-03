/* lpshim: the oracle's LD_PRELOAD library (OPEN-128, ADR-015 E7/E10).

   Every engine run of the oracle (scripts/tools/_oracle.py) is started with
   this library preloaded, and every process the engine starts (restricted
   \write18 commands, mktex*, their children) inherits it. It fixes the
   run-dependent inputs a document can observe that no environment variable
   fixes (OPEN-128 (1), the census in corpora/oracle_baseline/clock_census.json):

   THE CLOCK.  LP_CLOCK_EPOCH=E makes every wall-clock read of the process
     return E plus a per-process counter of microseconds, one per read:
     gettimeofday(2), time(2) and clock_gettime(2) of CLOCK_REALTIME,
     CLOCK_REALTIME_COARSE and CLOCK_TAI. So pdfTeX's \pdfrandomseed (seeded
     from gettimeofday), \pdfelapsedtime, \time/\day/\month/\year when
     FORCE_SOURCE_DATE is not set, and the dates any child program prints are
     functions of E and of the process's own sequence of reads. The counter
     advances, so a loop that waits for time to pass still ends. Other clocks
     (CLOCK_MONOTONIC, the CPU clocks) are not changed: pdfTeX does not import
     clock_gettime at all (MEASURED, its dynamic symbol table), and a timeout
     must keep measuring real time.
     LP_CLOCK="S.U,S.U,..." (the measurement entry point only; spike H.2's
     clockshim.c semantics, kept byte-compatible): gettimeofday returns these
     readings in call order and, when none is left, writes a message and exits
     with status 97. LP_CLOCK_LOG appends "N SEC USEC" per gettimeofday read.

   FILE TIMES.  With LP_CLOCK_EPOCH set, every stat-family call reports
     st_atime = st_mtime = st_ctime = E (and statx's four times): pdfTeX's
     \pdffilemoddate reads st_mtime, and a file the run itself wrote would
     otherwise carry the kernel's real time.

   THE KERNEL'S NAME.  With LP_CLOCK_EPOCH set, uname(2) reports a fixed
     release and version (a child such as java reports os.version); the
     node name is the container's, which the oracle fixes (--hostname).

   THE FILE-SYSTEM VIEW OF A TeX PROGRAM.  When LP_FS_ROOTS is set and the
     process's executable lies under LP_FS_EXE (the TeX Live binaries: pdfTeX
     itself, kpsewhich, bibtex, makeindex, METAFONT, luatex under l3sys-query,
     ...), every path the process opens, stats, lists or changes must resolve
     (symbolic links followed, `..` removed) inside one of the colon-separated
     LP_FS_ROOTS, or be /dev/null; any other path fails with ENOENT as if it
     did not exist. MEASURED before this library (2026-10-06, pinned image):
     under openin_any=p a document read /proc/uptime with \pdffiledump (the
     machine's uptime: the real clock), /proc/self/stat with \pdfmdfivesum
     (the pid and CPU times), and /etc/hostname and /etc/resolv.conf (the
     container's identity) with \pdfmdfivesum and \openin.
     LP_FS_LOG appends "deny OP PATH" for every refused path.
     LP_FS_HIDE (colon-separated) names trees OUTSIDE the roots whose
     METADATA is refused too (see allowed_at: the oracle's own mount points
     under /lp, where its bookkeeping lives).

   THE SHIM'S OWN BOOKKEEPING IS NEVER VISIBLE TO A TeX PROGRAM (OPEN-128,
     C-133). The directories of LP_SHIM_MARK, LP_FS_LOG and LP_CLOCK_LOG are
     refused -- content AND metadata, before the roots are consulted -- so a
     configuration that put them inside a root would still not show them.
     MEASURED before this rule (2026-11-03, review of 0400f74a): the marks
     were files named by pid in /tmp/lp/.shim, /tmp was a root, and a
     document saw, with \pdffilesize, a set of pids that differed between
     five identical runs, and that after a java child depended on the
     container's CPU count.

   DIRECTORY ORDER.  In every process of a fixed-clock run (LP_CLOCK_EPOCH;
     before C-138 in a TeX program only), readdir(3) returns a
     directory's entries sorted by name (bytewise), not in the file system's
     order: that order is the work root's (APFS through virtiofs on a Mac,
     ext4 hash order with a per-file-system seed on a CI runner, creation
     order on tmpfs), and a document reads it through `l3sys-query ls` in
     restricted \write18 (MEASURED: its `--sort date` breaks ties of the
     equal times above by the order it was given).

   PROOF OF LOADING.  With LP_SHIM_MARK=DIR, the constructor of the FIRST
     process the library loads into -- the engine: the supervisor preloads
     it into the engine alone, and every other shimmed process descends from
     the engine and starts after the engine's constructor ran -- creates
     DIR/engine (O_EXCL); every later process appends one line to
     DIR/children. Each holds "restricted" (the TeX file-system view) or
     "free". No name or content depends on a pid (C-133). The oracle's run
     supervisor refuses a run whose engine left no "restricted" mark (a
     preload the dynamic loader ignored would otherwise run the engine on the
     real clock); the children's counts are reported, not checked (C-136).

   THE USER (C-139 (b)).  With LP_CLOCK_EPOCH set, getuid/geteuid/getgid/
     getegid/getresuid/getresgid/getgroups report LP_ID (1000: the image's
     own user, `texlive`) for the run's real ids, and every stat-family call
     reports st_uid/st_gid = LP_ID for a file the run's user owns. The
     container runs as the HOST user (--user; colima's virtiofs and the CI
     runner's bind mount need it for the run directory), which was 501:20 on
     the Mac and the runner's uid in CI, and a child (perl's $<, Python's
     os.getuid, java's user.name) could print it.

   CPU TIME.  With LP_CLOCK_EPOCH set, the process and thread CPU clocks
     (clock_gettime of CLOCK_PROCESS_CPUTIME_ID / CLOCK_THREAD_CPUTIME_ID,
     clock(3), times(2)'s tms fields, getrusage(2)'s ru_utime/ru_stime) read
     a per-process counter of one microsecond per read, like the wall clock
     (C-137): CPU time is run-dependent and a child (gs's usertime, Lua's
     os.clock, Python's process_time) could print it. CLOCK_MONOTONIC and
     CLOCK_BOOTTIME stay real (timeouts and waits inside children use them;
     no program a document can start prints them: C-137).

   RANDOMNESS AND TEMPORARY NAMES (C-138).  With LP_CLOCK_EPOCH set, every
     process -- the TeX programs and the /usr/bin interpreters a restricted
     \write18 starts alike -- reads a DETERMINISTIC byte stream (splitmix64
     from a fixed seed, per process) from getrandom(2), getentropy(3) and an
     open of /dev/urandom, /dev/random or /dev/arandom (an anonymous memfd of
     LP_RANDOM_BYTES), and the mkstemp/mkostemp/mkstemps/mkdtemp/mktemp family
     fills its XXXXXX from a per-process counter, retrying on EEXIST. MEASURED
     before (review of 52b81823, 2026-11-03): gs under repstopdf -dSAFER may
     enumerate its own TMPDIR, which held gs_XXXXXX names from mkstemp64, and
     an EPS printed them into a PDF the document then hashed: two identical
     runs differed. Every reachable child's temporary names (gs and perl:
     mkstemp64; the JVM: mkstemp64; Python's tempfile: getrandom) and seeds
     are now functions of the run's own sequence of calls.

   Built by build.sh in a digest-pinned ubuntu:22.04; the two .so files'
   sha256 are pinned in _oracle.SHIM_SHA256 and checked before every
   session and inside every run. */
#define _GNU_SOURCE
#include <dirent.h>
#include <dlfcn.h>
#include <pthread.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/resource.h>
#include <sys/syscall.h>
#include <sys/times.h>
#include <sys/time.h>
#include <sys/utsname.h>
#include <time.h>
#include <unistd.h>

#define LP_ID 1000
#define LP_RELEASE "6.0.0-lp-oracle"
#define LP_VERSION "#1 SMP lp-oracle"

static int have_epoch;          /* LP_CLOCK_EPOCH set */
static long long epoch;
static unsigned long long ticks; /* microseconds handed out, per process */
static const char *readings;    /* LP_CLOCK (measurement only) */
static int readings_used;
static const char *clock_log;   /* LP_CLOCK_LOG */
static int restrict_fs;         /* this process is a TeX program */
static char roots[8][PATH_MAX];
static int nroots;
static const char *fs_log;      /* LP_FS_LOG */
static char hides[8][PATH_MAX];  /* LP_FS_HIDE: metadata refused too */
static int nhides;
static char privs[3][PATH_MAX];  /* the bookkeeping directories: always refused */
static int nprivs;
static unsigned long long cputicks; /* CPU-clock microseconds handed out */
static uid_t real_uid;
static gid_t real_gid;

static int split_paths(const char *r, char out[][PATH_MAX], int max)
{
  int n = 0;
  while (r && *r && n < max) {
    const char *c = strchr(r, ':');
    size_t len = c ? (size_t) (c - r) : strlen(r);
    if (len > 0 && len < PATH_MAX) {
      memcpy(out[n], r, len);
      out[n][len] = 0;
      n++;
    }
    if (!c) break;
    r = c + 1;
  }
  return n;
}

static void add_priv_dir(const char *path, int is_dir)
{
  if (!path || path[0] != '/' || nprivs >= 3) return;
  size_t len = strlen(path);
  if (len >= PATH_MAX) return;
  memcpy(privs[nprivs], path, len + 1);
  if (!is_dir) {
    char *sl = strrchr(privs[nprivs], '/');
    if (!sl || sl == privs[nprivs]) return;   /* never "/" itself */
    *sl = 0;
  }
  nprivs++;
}

static int under(const char *c, const char *root)
{
  size_t l = strlen(root);
  return strncmp(c, root, l) == 0 && (c[l] == 0 || c[l] == '/');
}

static void *real(const char *name)
{
  void *p = dlsym(RTLD_NEXT, name);
  return p;
}

static void lp_write_fd(int fd, const char *s)
{
  size_t n = strlen(s);
  while (n > 0) {
    ssize_t w = syscall(SYS_write, fd, s, n);
    if (w <= 0) return;
    s += w; n -= (size_t) w;
  }
}

__attribute__((constructor)) static void lp_init(void)
{
  const char *e = getenv("LP_CLOCK_EPOCH");
  if (e && *e) { have_epoch = 1; epoch = strtoll(e, NULL, 10); }
  readings = getenv("LP_CLOCK");
  if (readings && !*readings) readings = NULL;
  clock_log = getenv("LP_CLOCK_LOG");
  fs_log = getenv("LP_FS_LOG");
  const char *r = getenv("LP_FS_ROOTS"), *x = getenv("LP_FS_EXE");
  if (r && *r && x && *x) {
    char exe[PATH_MAX];
    ssize_t n = syscall(SYS_readlinkat, AT_FDCWD, "/proc/self/exe", exe, sizeof exe - 1);
    if (n > 0) {
      exe[n] = 0;
      if (strncmp(exe, x, strlen(x)) == 0) restrict_fs = 1;
    }
    nroots = split_paths(r, roots, 8);
    nhides = split_paths(getenv("LP_FS_HIDE"), hides, 8);
  }
  const char *m = getenv("LP_SHIM_MARK");
  real_uid = (uid_t) syscall(SYS_getuid);
  real_gid = (gid_t) syscall(SYS_getgid);
  add_priv_dir(m, 1);
  add_priv_dir(fs_log, 0);
  add_priv_dir(clock_log, 0);
  if (m && *m) {
    char p[PATH_MAX];
    char mode[PATH_MAX + 16], self[PATH_MAX];
    ssize_t sn = syscall(SYS_readlinkat, AT_FDCWD, "/proc/self/exe", self, sizeof self - 1);
    self[sn > 0 ? sn : 0] = 0;
    snprintf(mode, sizeof mode, "%s %s\n", restrict_fs ? "restricted" : "free", self);
    snprintf(p, sizeof p, "%s/engine", m);
    int fd = syscall(SYS_openat, AT_FDCWD, p, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC, 0644);
    if (fd < 0 && errno == EEXIST) {
      snprintf(p, sizeof p, "%s/children", m);
      fd = syscall(SYS_openat, AT_FDCWD, p, O_WRONLY | O_CREAT | O_APPEND | O_CLOEXEC, 0644);
    }
    if (fd >= 0) {
      lp_write_fd(fd, mode);
      syscall(SYS_close, fd);
    }
  }
}

/* ------------------------------------------------------------------ clock */

static void fixed_now(struct timespec *ts)
{
  unsigned long long n = __atomic_fetch_add(&ticks, 1, __ATOMIC_SEQ_CST);
  ts->tv_sec = (time_t) (epoch + (long long) (n / 1000000ULL));
  ts->tv_nsec = (long) ((n % 1000000ULL) * 1000ULL);
}

int gettimeofday(struct timeval *restrict tv, void *restrict tz)
{
  if (readings) {
    const char *p = readings;
    long long sec;
    long usec;
    int i;
    for (i = 0; i < readings_used; i++) {
      p = strchr(p, ',');
      if (!p) { lp_write_fd(2, "lp-clock: no clock reading left\n"); _exit(97); }
      p++;
    }
    if (sscanf(p, "%lld.%ld", &sec, &usec) != 2) { lp_write_fd(2, "lp-clock: bad reading\n"); _exit(97); }
    readings_used++;
    tv->tv_sec = (time_t) sec; tv->tv_usec = (suseconds_t) usec;
    if (clock_log) {
      char line[96];
      snprintf(line, sizeof line, "%d %lld %ld\n", readings_used, sec, usec);
      int fd = syscall(SYS_openat, AT_FDCWD, clock_log, O_WRONLY | O_CREAT | O_APPEND | O_CLOEXEC, 0644);
      if (fd >= 0) { lp_write_fd(fd, line); syscall(SYS_close, fd); }
    }
    return 0;
  }
  if (!have_epoch) {
    int (*f)(struct timeval *, void *) = real("gettimeofday");
    return f(tv, tz);
  }
  struct timespec ts;
  fixed_now(&ts);
  tv->tv_sec = ts.tv_sec; tv->tv_usec = (suseconds_t) (ts.tv_nsec / 1000);
  if (tz) memset(tz, 0, sizeof(struct timezone));
  if (clock_log) {
    char line[96];
    snprintf(line, sizeof line, "fixed %lld %ld\n", (long long) ts.tv_sec, (long) (ts.tv_nsec / 1000));
    int fd = syscall(SYS_openat, AT_FDCWD, clock_log, O_WRONLY | O_CREAT | O_APPEND | O_CLOEXEC, 0644);
    if (fd >= 0) { lp_write_fd(fd, line); syscall(SYS_close, fd); }
  }
  return 0;
}

time_t time(time_t *t)
{
  if (!have_epoch) {
    time_t (*f)(time_t *) = real("time");
    return f(t);
  }
  struct timespec ts;
  fixed_now(&ts);
  if (t) *t = ts.tv_sec;
  return ts.tv_sec;
}

static void cpu_now(struct timespec *ts)
{
  unsigned long long n = __atomic_fetch_add(&cputicks, 1, __ATOMIC_SEQ_CST);
  ts->tv_sec = (time_t) (n / 1000000ULL);
  ts->tv_nsec = (long) ((n % 1000000ULL) * 1000ULL);
}

int clock_gettime(clockid_t c, struct timespec *ts)
{
  if (have_epoch && (c == CLOCK_REALTIME || c == CLOCK_REALTIME_COARSE || c == CLOCK_TAI)) {
    if (ts) fixed_now(ts);
    return 0;
  }
  if (have_epoch && (c == CLOCK_PROCESS_CPUTIME_ID || c == CLOCK_THREAD_CPUTIME_ID)) {
    if (ts) cpu_now(ts);
    return 0;
  }
  int (*f)(clockid_t, struct timespec *) = real("clock_gettime");
  return f(c, ts);
}

/* ------------------------------------------------ randomness, temp names */

static int allowed_at(const char *op, int dirfd, const char *path);
#define ALLOWED(op, p) allowed_at(op, AT_FDCWD, p)

static unsigned long long rng_state = 0x6c702d6f7261636cULL; /* "lp-oracl" */
#define LP_RANDOM_BYTES (1u << 20)

static unsigned long long splitmix(void)
{
  unsigned long long z = __atomic_add_fetch(&rng_state, 0x9e3779b97f4a7c15ULL, __ATOMIC_SEQ_CST);
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
  return z ^ (z >> 31);
}

static void fill_random(void *buf, size_t n)
{
  unsigned char *b = buf;
  while (n > 0) {
    unsigned long long v = splitmix();
    size_t k = n < 8 ? n : 8;
    memcpy(b, &v, k);
    b += k; n -= k;
  }
}

ssize_t getrandom(void *buf, size_t n, unsigned int flags)
{
  if (!have_epoch) {
    ssize_t (*f)(void *, size_t, unsigned int) = real("getrandom");
    if (f) return f(buf, n, flags);
    return syscall(SYS_getrandom, buf, n, flags);
  }
  fill_random(buf, n);
  return (ssize_t) n;
}

int getentropy(void *buf, size_t n)
{
  if (!have_epoch) {
    int (*f)(void *, size_t) = real("getentropy");
    return f(buf, n);
  }
  if (n > 256) { errno = EIO; return -1; }
  fill_random(buf, n);
  return 0;
}

static int is_random_device(const char *p)
{
  return p && (strcmp(p, "/dev/urandom") == 0 || strcmp(p, "/dev/random") == 0
               || strcmp(p, "/dev/arandom") == 0);
}

/* A memfd holding LP_RANDOM_BYTES of the deterministic stream, positioned at
   0; -1 (errno EIO) if it cannot be made: fail closed, never the real device. */
static int random_fd(void)
{
  int fd = syscall(SYS_memfd_create, "lp-random", 1u /* MFD_CLOEXEC */);
  if (fd < 0) { errno = EIO; return -1; }
  unsigned char chunk[4096];
  for (unsigned int done = 0; done < LP_RANDOM_BYTES; done += sizeof chunk) {
    fill_random(chunk, sizeof chunk);
    if (syscall(SYS_write, fd, chunk, sizeof chunk) != (long) sizeof chunk) {
      syscall(SYS_close, fd); errno = EIO; return -1;
    }
  }
  if (lseek(fd, 0, SEEK_SET) != 0) { syscall(SYS_close, fd); errno = EIO; return -1; }
  return fd;
}
#define RANDOM_DEV(p) if (have_epoch && is_random_device(p)) return random_fd()

static unsigned long long tmp_counter;

/* Fill the six X's before `suffixlen` trailing bytes of `t` with the next
   value of the per-process counter and call `make` until it does not fail
   with EEXIST. */
static int lp_tempname(char *t, int suffixlen, int (*make)(const char *, int), int arg)
{
  size_t len = strlen(t);
  if (suffixlen < 0 || len < 6 + (size_t) suffixlen
      || memcmp(t + len - suffixlen - 6, "XXXXXX", 6) != 0) {
    errno = EINVAL; return -1;
  }
  char *x = t + len - suffixlen - 6;
  static const char digits[] = "0123456789abcdefghijklmnopqrstuvwxyz";
  for (unsigned int tries = 0; tries < 1000000; tries++) {
    unsigned long long v = __atomic_fetch_add(&tmp_counter, 1, __ATOMIC_SEQ_CST);
    for (int i = 5; i >= 0; i--) { x[i] = digits[v % 36]; v /= 36; }
    int rc = make(t, arg);
    if (rc >= 0 || errno != EEXIST) return rc;
  }
  errno = EEXIST;
  return -1;
}

static int make_file(const char *p, int flags)
{
  return syscall(SYS_openat, AT_FDCWD, p, O_RDWR | O_CREAT | O_EXCL | (flags & ~O_ACCMODE), 0600);
}
static int make_dir(const char *p, int unused)
{
  return syscall(SYS_mkdirat, AT_FDCWD, p, 0700);
}
static int make_none(const char *p, int unused)
{
  struct stat st;
  if (syscall(SYS_newfstatat, AT_FDCWD, p, &st, AT_SYMLINK_NOFOLLOW) == 0) { errno = EEXIST; return -1; }
  return 0;
}

int mkstemp(char *t) {
  if (!have_epoch) { int (*f)(char *) = real("mkstemp"); return f(t); }
  if (!ALLOWED("mkstemp", t)) return -1;
  return lp_tempname(t, 0, make_file, 0);
}
int mkstemp64(char *t) {
  if (!have_epoch) { int (*f)(char *) = real("mkstemp64"); return f(t); }
  if (!ALLOWED("mkstemp", t)) return -1;
  return lp_tempname(t, 0, make_file, 0);
}
int mkostemp(char *t, int fl) {
  if (!have_epoch) { int (*f)(char *, int) = real("mkostemp"); return f(t, fl); }
  if (!ALLOWED("mkstemp", t)) return -1;
  return lp_tempname(t, 0, make_file, fl);
}
int mkostemp64(char *t, int fl) {
  if (!have_epoch) { int (*f)(char *, int) = real("mkostemp64"); return f(t, fl); }
  if (!ALLOWED("mkstemp", t)) return -1;
  return lp_tempname(t, 0, make_file, fl);
}
int mkstemps(char *t, int sl) {
  if (!have_epoch) { int (*f)(char *, int) = real("mkstemps"); return f(t, sl); }
  if (!ALLOWED("mkstemp", t)) return -1;
  return lp_tempname(t, sl, make_file, 0);
}
int mkstemps64(char *t, int sl) {
  if (!have_epoch) { int (*f)(char *, int) = real("mkstemps64"); return f(t, sl); }
  if (!ALLOWED("mkstemp", t)) return -1;
  return lp_tempname(t, sl, make_file, 0);
}
int mkostemps(char *t, int sl, int fl) {
  if (!have_epoch) { int (*f)(char *, int, int) = real("mkostemps"); return f(t, sl, fl); }
  if (!ALLOWED("mkstemp", t)) return -1;
  return lp_tempname(t, sl, make_file, fl);
}
int mkostemps64(char *t, int sl, int fl) {
  if (!have_epoch) { int (*f)(char *, int, int) = real("mkostemps64"); return f(t, sl, fl); }
  if (!ALLOWED("mkstemp", t)) return -1;
  return lp_tempname(t, sl, make_file, fl);
}
char *mkdtemp(char *t) {
  if (!have_epoch) { char *(*f)(char *) = real("mkdtemp"); return f(t); }
  if (!ALLOWED("mkdir", t)) return NULL;
  return lp_tempname(t, 0, make_dir, 0) == 0 ? t : NULL;
}
char *mktemp(char *t) {
  if (!have_epoch) { char *(*f)(char *) = real("mktemp"); return f(t); }
  if (lp_tempname(t, 0, make_none, 0) != 0) t[0] = 0;
  return t;
}

clock_t clock(void)
{
  if (!have_epoch) {
    clock_t (*f)(void) = real("clock");
    return f();
  }
  struct timespec ts;
  cpu_now(&ts);
  return (clock_t) ((long long) ts.tv_sec * CLOCKS_PER_SEC + ts.tv_nsec / (1000000000L / CLOCKS_PER_SEC));
}

clock_t times(struct tms *t)
{
  clock_t (*f)(struct tms *) = real("times");
  clock_t rc = f(t);
  if (have_epoch && t) {
    struct timespec ts;
    cpu_now(&ts);
    long hz = sysconf(_SC_CLK_TCK);
    clock_t v = (clock_t) ((long long) ts.tv_sec * hz + ts.tv_nsec / (1000000000L / (hz > 0 ? hz : 100)));
    t->tms_utime = v; t->tms_stime = 0; t->tms_cutime = 0; t->tms_cstime = 0;
  }
  return rc;
}

int getrusage(int who, struct rusage *u)
{
  int (*f)(int, struct rusage *) = real("getrusage");
  int rc = f(who, u);
  if (rc == 0 && have_epoch && u) {
    struct timespec ts;
    cpu_now(&ts);
    u->ru_utime.tv_sec = ts.tv_sec; u->ru_utime.tv_usec = ts.tv_nsec / 1000;
    u->ru_stime.tv_sec = 0; u->ru_stime.tv_usec = 0;
  }
  return rc;
}

#define ID_FN(name, type, realexpr)                                \
  type name(void) {                                               \
    type (*f)(void) = real(#name);                                \
    type v = f();                                                 \
    return (have_epoch && v == (realexpr)) ? (type) LP_ID : v;    \
  }
ID_FN(getuid, uid_t, real_uid)
ID_FN(geteuid, uid_t, real_uid)
ID_FN(getgid, gid_t, real_gid)
ID_FN(getegid, gid_t, real_gid)

int getresuid(uid_t *r, uid_t *e, uid_t *s)
{
  int (*f)(uid_t *, uid_t *, uid_t *) = real("getresuid");
  int rc = f(r, e, s);
  if (rc == 0 && have_epoch) {
    if (r && *r == real_uid) *r = LP_ID;
    if (e && *e == real_uid) *e = LP_ID;
    if (s && *s == real_uid) *s = LP_ID;
  }
  return rc;
}
int getresgid(gid_t *r, gid_t *e, gid_t *s)
{
  int (*f)(gid_t *, gid_t *, gid_t *) = real("getresgid");
  int rc = f(r, e, s);
  if (rc == 0 && have_epoch) {
    if (r && *r == real_gid) *r = LP_ID;
    if (e && *e == real_gid) *e = LP_ID;
    if (s && *s == real_gid) *s = LP_ID;
  }
  return rc;
}
int getgroups(int n, gid_t *g)
{
  int (*f)(int, gid_t *) = real("getgroups");
  int rc = f(n, g);
  if (rc > 0 && have_epoch && n > 0 && g)
    for (int i = 0; i < rc; i++) if (g[i] == real_gid) g[i] = LP_ID;
  return rc;
}

int uname(struct utsname *u)
{
  int (*f)(struct utsname *) = real("uname");
  int rc = f(u);
  if (rc == 0 && have_epoch && u) {
    snprintf(u->release, sizeof u->release, "%s", LP_RELEASE);
    snprintf(u->version, sizeof u->version, "%s", LP_VERSION);
  }
  return rc;
}

/* --------------------------------------------------------- file-system view */

static void lexical(char *p)
{
  /* remove "." and ".." components and repeated slashes of an absolute path */
  char out[PATH_MAX * 2];
  size_t o = 0;
  const char *s = p;
  out[0] = 0;
  while (*s) {
    while (*s == '/') s++;
    if (!*s) break;
    const char *e = strchr(s, '/');
    size_t len = e ? (size_t) (e - s) : strlen(s);
    if (len == 1 && s[0] == '.') {
      /* nothing */
    } else if (len == 2 && s[0] == '.' && s[1] == '.') {
      while (o > 0 && out[o - 1] != '/') o--;
      if (o > 0) o--;
      out[o] = 0;
    } else if (o + 1 + len < sizeof out) {
      out[o++] = '/';
      memcpy(out + o, s, len);
      o += len;
      out[o] = 0;
    }
    s += len;
  }
  if (o == 0) { out[0] = '/'; out[1] = 0; }
  snprintf(p, PATH_MAX * 2, "%s", out);
}

/* The canonical absolute form of `path` (relative to `dirfd`): realpath of the
   path, else of its parent plus the last component, else lexical. */
static void canonical(int dirfd, const char *path, char *out)
{
  char abs[PATH_MAX * 2];
  if (path[0] == '/') {
    snprintf(abs, sizeof abs, "%s", path);
  } else {
    char base[PATH_MAX];
    base[0] = 0;
    if (dirfd == AT_FDCWD) {
      if (!getcwd(base, sizeof base)) base[0] = 0;
    } else {
      char fdp[64];
      snprintf(fdp, sizeof fdp, "/proc/self/fd/%d", dirfd);
      ssize_t n = syscall(SYS_readlinkat, AT_FDCWD, fdp, base, sizeof base - 1);
      base[n > 0 ? n : 0] = 0;
    }
    snprintf(abs, sizeof abs, "%s/%s", base, path);
  }
  char r[PATH_MAX];
  if (realpath(abs, r)) { snprintf(out, PATH_MAX * 2, "%s", r); return; }
  lexical(abs);
  char *slash = strrchr(abs, '/');
  if (slash && slash != abs) {
    *slash = 0;
    if (realpath(abs, r)) {
      *slash = '/';
      snprintf(out, PATH_MAX * 2, "%s%s", r, slash);
      return;
    }
    *slash = '/';
  }
  snprintf(out, PATH_MAX * 2, "%s", abs);
}

static int allowed_at(const char *op, int dirfd, const char *path)
{ /* forward-declared above */
  int meta = strstr(op, "stat") != NULL || strcmp(op, "access") == 0;
  if (!restrict_fs || !path) return 1;
  if (!*path) return 1;   /* the call fails with ENOENT by itself */
  char c[PATH_MAX * 2];
  canonical(dirfd, path, c);
  int priv = 0;
  for (int i = 0; i < nprivs; i++)
    if (under(c, privs[i])) { priv = 1; break; }
  if (!priv) {
    if (strcmp(c, "/dev/null") == 0) return 1;
    for (int i = 0; i < nroots; i++)
      if (under(c, roots[i])) return 1;
    for (int i = 0; i < nhides; i++)
      if (under(c, hides[i])) { meta = 0; break; }
  } else {
    meta = 0;
  }
  /* METADATA (stat, lstat, access) of a path on the image's own read-only
     root file system is allowed; its CONTENT is not. kpathsea locates itself
     by searching PATH and lstat-ing every component of the binary's path
     (MEASURED: a denied lstat("/usr"), then "/usr/bin", stopped pdfTeX before
     it read a byte), and so does every TeX program a restricted \write18
     starts by name. What the image holds is fixed by its digest, and the
     times are fixed below; what docker or the kernel puts into a container
     is not, and stays refused: /proc, /sys, /dev, the files docker writes per
     container (/etc/hostname, /etc/hosts, /etc/resolv.conf, /etc/mtab) and
     the init binary it bind-mounts from the host (/sbin/docker-init), the
     shim's own bookkeeping (privs: above) and every LP_FS_HIDE tree (the
     oracle's mount points under /lp other than the run directory: C-133). */
  if (meta) {
    static const char *const volatile_paths[] = {
      "/proc", "/sys", "/dev", "/run", "/var/run", "/etc/hostname", "/etc/hosts",
      "/etc/resolv.conf", "/etc/mtab", "/sbin/docker-init", "/usr/sbin/docker-init",
      "/.dockerenv", NULL };
    int vol = 0;
    for (int i = 0; volatile_paths[i]; i++) {
      size_t l = strlen(volatile_paths[i]);
      if (strncmp(c, volatile_paths[i], l) == 0 && (c[l] == 0 || c[l] == '/')) { vol = 1; break; }
    }
    if (!vol) return 1;
  }
  if (fs_log) {
    char line[PATH_MAX * 2 + 64];
    snprintf(line, sizeof line, "deny %s %s\n", op, c);
    int fd = syscall(SYS_openat, AT_FDCWD, fs_log, O_WRONLY | O_CREAT | O_APPEND | O_CLOEXEC, 0644);
    if (fd >= 0) { lp_write_fd(fd, line); syscall(SYS_close, fd); }
  }
  errno = ENOENT;
  return 0;
}
#define ALLOWED(op, p) allowed_at(op, AT_FDCWD, p)

static void sdir_load(DIR *d);
/* C-138: every process of a fixed-clock run lists directories sorted, not
   only the TeX programs: the /usr/bin interpreters' children list the run
   directory too, whose order is the work root's file system's. */
#define SORT_DIRS (restrict_fs || have_epoch)

static void fix_stat(struct stat *st)
{
  if (!have_epoch || !st) return;
  if (st->st_uid == real_uid) st->st_uid = LP_ID;
  if (st->st_gid == real_gid) st->st_gid = LP_ID;
  st->st_atim.tv_sec = st->st_mtim.tv_sec = st->st_ctim.tv_sec = (time_t) epoch;
  st->st_atim.tv_nsec = st->st_mtim.tv_nsec = st->st_ctim.tv_nsec = 0;
}

#define OPEN_MODE(flags, mode)                          \
  mode_t mode = 0;                                      \
  if ((flags) & (O_CREAT | __O_TMPFILE)) {              \
    va_list ap; va_start(ap, flags);                    \
    mode = va_arg(ap, mode_t); va_end(ap);              \
  }

int open(const char *p, int flags, ...)
{
  OPEN_MODE(flags, mode);
  if (!ALLOWED("open", p)) return -1;
  RANDOM_DEV(p);
  int (*f)(const char *, int, ...) = real("open");
  return f(p, flags, mode);
}
int open64(const char *p, int flags, ...)
{
  OPEN_MODE(flags, mode);
  if (!ALLOWED("open", p)) return -1;
  RANDOM_DEV(p);
  int (*f)(const char *, int, ...) = real("open64");
  return f(p, flags, mode);
}
int openat(int d, const char *p, int flags, ...)
{
  OPEN_MODE(flags, mode);
  if (!allowed_at("openat", d, p)) return -1;
  if (p[0] == '/') RANDOM_DEV(p);
  int (*f)(int, const char *, int, ...) = real("openat");
  return f(d, p, flags, mode);
}
int openat64(int d, const char *p, int flags, ...)
{
  OPEN_MODE(flags, mode);
  if (!allowed_at("openat", d, p)) return -1;
  if (p[0] == '/') RANDOM_DEV(p);
  int (*f)(int, const char *, int, ...) = real("openat64");
  return f(d, p, flags, mode);
}
int __open_2(const char *p, int flags)
{
  if (!ALLOWED("open", p)) return -1;
  RANDOM_DEV(p);
  int (*f)(const char *, int) = real("__open_2");
  return f(p, flags);
}
int __open64_2(const char *p, int flags)
{
  if (!ALLOWED("open", p)) return -1;
  RANDOM_DEV(p);
  int (*f)(const char *, int) = real("__open64_2");
  return f(p, flags);
}
int __openat_2(int d, const char *p, int flags)
{
  if (!allowed_at("openat", d, p)) return -1;
  if (p[0] == '/') RANDOM_DEV(p);
  int (*f)(int, const char *, int) = real("__openat_2");
  return f(d, p, flags);
}
int __openat64_2(int d, const char *p, int flags)
{
  if (!allowed_at("openat", d, p)) return -1;
  if (p[0] == '/') RANDOM_DEV(p);
  int (*f)(int, const char *, int) = real("__openat64_2");
  return f(d, p, flags);
}
int creat(const char *p, mode_t m)
{
  if (!ALLOWED("creat", p)) return -1;
  int (*f)(const char *, mode_t) = real("creat");
  return f(p, m);
}
int creat64(const char *p, mode_t m)
{
  if (!ALLOWED("creat", p)) return -1;
  int (*f)(const char *, mode_t) = real("creat64");
  return f(p, m);
}
FILE *fopen(const char *p, const char *m)
{
  if (!ALLOWED("fopen", p)) return NULL;
  if (have_epoch && is_random_device(p)) {
    int fd = random_fd();
    return fd < 0 ? NULL : fdopen(fd, "r");
  }
  FILE *(*f)(const char *, const char *) = real("fopen");
  return f(p, m);
}
FILE *fopen64(const char *p, const char *m)
{
  if (!ALLOWED("fopen", p)) return NULL;
  if (have_epoch && is_random_device(p)) {
    int fd = random_fd();
    return fd < 0 ? NULL : fdopen(fd, "r");
  }
  FILE *(*f)(const char *, const char *) = real("fopen64");
  return f(p, m);
}
FILE *freopen(const char *p, const char *m, FILE *s)
{
  if (!ALLOWED("freopen", p)) return NULL;
  FILE *(*f)(const char *, const char *, FILE *) = real("freopen");
  return f(p, m, s);
}
FILE *freopen64(const char *p, const char *m, FILE *s)
{
  if (!ALLOWED("freopen", p)) return NULL;
  FILE *(*f)(const char *, const char *, FILE *) = real("freopen64");
  return f(p, m, s);
}
DIR *opendir(const char *p)
{
  if (!ALLOWED("opendir", p)) return NULL;
  DIR *(*f)(const char *) = real("opendir");
  DIR *d = f(p);
  if (d && SORT_DIRS) sdir_load(d);
  return d;
}
/* sorted directory streams (restricted processes only) */
struct sdir {
  DIR *d;
  struct dirent **ents;
  size_t n, i;
  struct sdir *next;
};
static struct sdir *sdirs;
static pthread_mutex_t sdir_mu = PTHREAD_MUTEX_INITIALIZER;

static int dirent_cmp(const void *a, const void *b)
{
  const struct dirent *x = *(const struct dirent *const *) a, *y = *(const struct dirent *const *) b;
  return strcmp(x->d_name, y->d_name);
}

static void sdir_load(DIR *d)
{
  struct dirent *(*rd)(DIR *) = real("readdir");
  struct sdir *s = calloc(1, sizeof *s);
  size_t cap = 0;
  struct dirent *e;
  if (!s || !rd) { free(s); return; }
  s->d = d;
  while ((e = rd(d)) != NULL) {
    if (s->n == cap) {
      size_t nc = cap ? cap * 2 : 64;
      struct dirent **ne = realloc(s->ents, nc * sizeof *ne);
      if (!ne) break;
      s->ents = ne; cap = nc;
    }
    struct dirent *c = malloc(sizeof *c);
    if (!c) break;
    memcpy(c, e, sizeof *c);
    s->ents[s->n++] = c;
  }
  qsort(s->ents, s->n, sizeof *s->ents, dirent_cmp);
  pthread_mutex_lock(&sdir_mu);
  s->next = sdirs; sdirs = s;
  pthread_mutex_unlock(&sdir_mu);
}

static struct sdir *sdir_find(DIR *d, int unlink_it)
{
  struct sdir **pp, *s = NULL;
  pthread_mutex_lock(&sdir_mu);
  for (pp = &sdirs; *pp; pp = &(*pp)->next) {
    if ((*pp)->d == d) {
      s = *pp;
      if (unlink_it) *pp = s->next;
      break;
    }
  }
  pthread_mutex_unlock(&sdir_mu);
  return s;
}

DIR *fdopendir(int fd)
{
  DIR *(*f)(int) = real("fdopendir");
  DIR *d = f(fd);
  if (d && SORT_DIRS) sdir_load(d);
  return d;
}

struct dirent *readdir(DIR *d)
{
  struct sdir *s = SORT_DIRS ? sdir_find(d, 0) : NULL;
  if (s) return s->i < s->n ? s->ents[s->i++] : NULL;
  struct dirent *(*f)(DIR *) = real("readdir");
  return f(d);
}

struct dirent64 *readdir64(DIR *d)
{
  struct sdir *s = SORT_DIRS ? sdir_find(d, 0) : NULL;
  if (s) return s->i < s->n ? (struct dirent64 *) s->ents[s->i++] : NULL;
  struct dirent64 *(*f)(DIR *) = real("readdir64");
  return f(d);
}

void rewinddir(DIR *d)
{
  struct sdir *s = SORT_DIRS ? sdir_find(d, 0) : NULL;
  if (s) s->i = 0;
  void (*f)(DIR *) = real("rewinddir");
  f(d);
}

/* scandir(3) with no comparison function returns readdir's order, which
   glibc's own scandir takes from its internal readdir (not the one above):
   sorted here too (C-138). */
static int dirent_ptr_cmp(const void *a, const void *b)
{
  return strcmp((*(struct dirent *const *) a)->d_name, (*(struct dirent *const *) b)->d_name);
}
int scandir(const char *p, struct dirent ***nl, int (*sel)(const struct dirent *),
            int (*cmp)(const struct dirent **, const struct dirent **))
{
  if (!ALLOWED("opendir", p)) return -1;
  int (*f)(const char *, struct dirent ***, int (*)(const struct dirent *),
           int (*)(const struct dirent **, const struct dirent **)) = real("scandir");
  int n = f(p, nl, sel, cmp);
  if (n > 1 && !cmp && SORT_DIRS) qsort(*nl, (size_t) n, sizeof **nl, dirent_ptr_cmp);
  return n;
}
int scandir64(const char *p, struct dirent64 ***nl, int (*sel)(const struct dirent64 *),
              int (*cmp)(const struct dirent64 **, const struct dirent64 **))
{
  if (!ALLOWED("opendir", p)) return -1;
  int (*f)(const char *, struct dirent64 ***, int (*)(const struct dirent64 *),
           int (*)(const struct dirent64 **, const struct dirent64 **)) = real("scandir64");
  int n = f(p, nl, sel, cmp);
  if (n > 1 && !cmp && SORT_DIRS) qsort(*nl, (size_t) n, sizeof **nl, dirent_ptr_cmp);
  return n;
}

int closedir(DIR *d)
{
  struct sdir *s = SORT_DIRS ? sdir_find(d, 1) : NULL;
  if (s) {
    for (size_t i = 0; i < s->n; i++) free(s->ents[i]);
    free(s->ents);
    free(s);
  }
  int (*f)(DIR *) = real("closedir");
  return f(d);
}

int access(const char *p, int m)
{
  if (!ALLOWED("access", p)) return -1;
  int (*f)(const char *, int) = real("access");
  return f(p, m);
}
int euidaccess(const char *p, int m)
{
  if (!ALLOWED("access", p)) return -1;
  int (*f)(const char *, int) = real("euidaccess");
  return f(p, m);
}
int eaccess(const char *p, int m)
{
  if (!ALLOWED("access", p)) return -1;
  int (*f)(const char *, int) = real("eaccess");
  return f(p, m);
}
int faccessat(int d, const char *p, int m, int fl)
{
  if (!allowed_at("access", d, p)) return -1;
  int (*f)(int, const char *, int, int) = real("faccessat");
  return f(d, p, m, fl);
}
int mkdir(const char *p, mode_t m)
{
  if (!ALLOWED("mkdir", p)) return -1;
  int (*f)(const char *, mode_t) = real("mkdir");
  return f(p, m);
}
int mkdirat(int d, const char *p, mode_t m)
{
  if (!allowed_at("mkdir", d, p)) return -1;
  int (*f)(int, const char *, mode_t) = real("mkdirat");
  return f(d, p, m);
}
int rmdir(const char *p)
{
  if (!ALLOWED("rmdir", p)) return -1;
  int (*f)(const char *) = real("rmdir");
  return f(p);
}
int unlink(const char *p)
{
  if (!ALLOWED("unlink", p)) return -1;
  int (*f)(const char *) = real("unlink");
  return f(p);
}
int unlinkat(int d, const char *p, int fl)
{
  if (!allowed_at("unlink", d, p)) return -1;
  int (*f)(int, const char *, int) = real("unlinkat");
  return f(d, p, fl);
}
int remove(const char *p)
{
  if (!ALLOWED("remove", p)) return -1;
  int (*f)(const char *) = real("remove");
  return f(p);
}
int rename(const char *a, const char *b)
{
  if (!ALLOWED("rename", a) || !ALLOWED("rename", b)) return -1;
  int (*f)(const char *, const char *) = real("rename");
  return f(a, b);
}
int renameat(int da, const char *a, int db, const char *b)
{
  if (!allowed_at("rename", da, a) || !allowed_at("rename", db, b)) return -1;
  int (*f)(int, const char *, int, const char *) = real("renameat");
  return f(da, a, db, b);
}

/* stat family: the path check, then the fixed times. On glibc >= 2.33 stat,
   lstat, fstatat (and their 64 forms) are real functions; binaries built
   against an older glibc (pdfTeX: __xstat, __lxstat, MEASURED) call the
   versioned __xstat family, whose layout for _STAT_VER is struct stat. */
int stat(const char *p, struct stat *st)
{
  if (!ALLOWED("stat", p)) return -1;
  int (*f)(const char *, struct stat *) = real("stat");
  int rc = f(p, st);
  if (rc == 0) fix_stat(st);
  return rc;
}
int lstat(const char *p, struct stat *st)
{
  if (!ALLOWED("lstat", p)) return -1;
  int (*f)(const char *, struct stat *) = real("lstat");
  int rc = f(p, st);
  if (rc == 0) fix_stat(st);
  return rc;
}
int fstat(int fd, struct stat *st)
{
  int (*f)(int, struct stat *) = real("fstat");
  int rc = f(fd, st);
  if (rc == 0) fix_stat(st);
  return rc;
}
int fstatat(int d, const char *p, struct stat *st, int fl)
{
  if (!((fl & AT_EMPTY_PATH) && !*p) && !allowed_at("fstatat", d, p)) return -1;
  int (*f)(int, const char *, struct stat *, int) = real("fstatat");
  int rc = f(d, p, st, fl);
  if (rc == 0) fix_stat(st);
  return rc;
}
int stat64(const char *p, struct stat64 *st)
{
  if (!ALLOWED("stat", p)) return -1;
  int (*f)(const char *, struct stat64 *) = real("stat64");
  int rc = f(p, st);
  if (rc == 0) fix_stat((struct stat *) st);
  return rc;
}
int lstat64(const char *p, struct stat64 *st)
{
  if (!ALLOWED("lstat", p)) return -1;
  int (*f)(const char *, struct stat64 *) = real("lstat64");
  int rc = f(p, st);
  if (rc == 0) fix_stat((struct stat *) st);
  return rc;
}
int fstat64(int fd, struct stat64 *st)
{
  int (*f)(int, struct stat64 *) = real("fstat64");
  int rc = f(fd, st);
  if (rc == 0) fix_stat((struct stat *) st);
  return rc;
}
int fstatat64(int d, const char *p, struct stat64 *st, int fl)
{
  if (!((fl & AT_EMPTY_PATH) && !*p) && !allowed_at("fstatat", d, p)) return -1;
  int (*f)(int, const char *, struct stat64 *, int) = real("fstatat64");
  int rc = f(d, p, st, fl);
  if (rc == 0) fix_stat((struct stat *) st);
  return rc;
}
int __xstat(int ver, const char *p, struct stat *st)
{
  if (!ALLOWED("stat", p)) return -1;
  int (*f)(int, const char *, struct stat *) = real("__xstat");
  int rc;
  if (f) rc = f(ver, p, st);
  else { int (*g)(const char *, struct stat *) = real("stat"); rc = g(p, st); }
  if (rc == 0) fix_stat(st);
  return rc;
}
int __lxstat(int ver, const char *p, struct stat *st)
{
  if (!ALLOWED("lstat", p)) return -1;
  int (*f)(int, const char *, struct stat *) = real("__lxstat");
  int rc;
  if (f) rc = f(ver, p, st);
  else { int (*g)(const char *, struct stat *) = real("lstat"); rc = g(p, st); }
  if (rc == 0) fix_stat(st);
  return rc;
}
int __fxstat(int ver, int fd, struct stat *st)
{
  int (*f)(int, int, struct stat *) = real("__fxstat");
  int rc;
  if (f) rc = f(ver, fd, st);
  else { int (*g)(int, struct stat *) = real("fstat"); rc = g(fd, st); }
  if (rc == 0) fix_stat(st);
  return rc;
}
int __fxstatat(int ver, int d, const char *p, struct stat *st, int fl)
{
  if (!((fl & AT_EMPTY_PATH) && !*p) && !allowed_at("fstatat", d, p)) return -1;
  int (*f)(int, int, const char *, struct stat *, int) = real("__fxstatat");
  int rc;
  if (f) rc = f(ver, d, p, st, fl);
  else { int (*g)(int, const char *, struct stat *, int) = real("fstatat"); rc = g(d, p, st, fl); }
  if (rc == 0) fix_stat(st);
  return rc;
}
int __xstat64(int ver, const char *p, struct stat64 *st)
{
  if (!ALLOWED("stat", p)) return -1;
  int (*f)(int, const char *, struct stat64 *) = real("__xstat64");
  int rc;
  if (f) rc = f(ver, p, st);
  else { int (*g)(const char *, struct stat64 *) = real("stat64"); rc = g(p, st); }
  if (rc == 0) fix_stat((struct stat *) st);
  return rc;
}
int __lxstat64(int ver, const char *p, struct stat64 *st)
{
  if (!ALLOWED("lstat", p)) return -1;
  int (*f)(int, const char *, struct stat64 *) = real("__lxstat64");
  int rc;
  if (f) rc = f(ver, p, st);
  else { int (*g)(const char *, struct stat64 *) = real("lstat64"); rc = g(p, st); }
  if (rc == 0) fix_stat((struct stat *) st);
  return rc;
}
int __fxstat64(int ver, int fd, struct stat64 *st)
{
  int (*f)(int, int, struct stat64 *) = real("__fxstat64");
  int rc;
  if (f) rc = f(ver, fd, st);
  else { int (*g)(int, struct stat64 *) = real("fstat64"); rc = g(fd, st); }
  if (rc == 0) fix_stat((struct stat *) st);
  return rc;
}
int __fxstatat64(int ver, int d, const char *p, struct stat64 *st, int fl)
{
  if (!((fl & AT_EMPTY_PATH) && !*p) && !allowed_at("fstatat", d, p)) return -1;
  int (*f)(int, int, const char *, struct stat64 *, int) = real("__fxstatat64");
  int rc;
  if (f) rc = f(ver, d, p, st, fl);
  else { int (*g)(int, const char *, struct stat64 *, int) = real("fstatat64"); rc = g(d, p, st, fl); }
  if (rc == 0) fix_stat((struct stat *) st);
  return rc;
}

#ifdef STATX_BASIC_STATS
int statx(int d, const char *p, int fl, unsigned int mask, struct statx *sx)
{
  if (!((fl & AT_EMPTY_PATH) && !*p) && !allowed_at("statx", d, p)) return -1;
  int (*f)(int, const char *, int, unsigned int, struct statx *) = real("statx");
  int rc = f(d, p, fl, mask, sx);
  if (rc == 0 && have_epoch) {
    sx->stx_atime.tv_sec = sx->stx_mtime.tv_sec = sx->stx_ctime.tv_sec = sx->stx_btime.tv_sec = epoch;
    sx->stx_atime.tv_nsec = sx->stx_mtime.tv_nsec = sx->stx_ctime.tv_nsec = sx->stx_btime.tv_nsec = 0;
    if (sx->stx_uid == real_uid) sx->stx_uid = LP_ID;
    if (sx->stx_gid == real_gid) sx->stx_gid = LP_ID;
  }
  return rc;
}
#endif
