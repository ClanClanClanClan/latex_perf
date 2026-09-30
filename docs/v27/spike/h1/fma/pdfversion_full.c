/* The FMA site in read_pdf_info (pdftoepdf.cc, r78081):
 *     float pdf_version_wanted = major_pdf_version_wanted + (minor_pdf_version_wanted * 0.1);
 * aarch64 computes fma(minor, 0.1, major) then rounds to float; x86_64 rounds the
 * product, adds, then rounds to float.  pdfTeX's check_pdfversion (pdftex.web
 * 15463-15484) enforces major >= 1 and minor in 0..9; major has no upper bound
 * below the integer range.  This program checks EVERY pair in that range:
 * major in [1, 2^31-1], minor in 0..9 (21,474,836,470 pairs).
 * Build with contraction OFF so the unfused expression stays unfused:
 *     cc -O2 -ffp-contract=off -o pdfversion_full pdfversion_full.c -lm   */
#include <math.h>
#include <stdio.h>
#include <stdint.h>
int main(void) {
    uint64_t pairs = 0, bad = 0;
    for (int64_t M = 1; M <= 2147483647LL; M++) {
        double dm = (double) M;
        for (int m = 0; m <= 9; m++) {
            float unfused = (float) (dm + ((double) m * 0.1));
            float fused = (float) fma((double) m, 0.1, dm);
            pairs++;
            if (unfused != fused) {
                if (bad < 10) printf("differ: major=%lld minor=%d\n", (long long) M, m);
                bad++;
            }
        }
    }
    /* self-check 1: the SAME loop body, over an out-of-range block where differences
     * exist (minor -1000..-1, major 1..20000), must count exactly what the independent
     * Python transcription (pdfversion_exhaustive.py, math.fma) counts: 20000 pairs,
     * minor = -10*major for major 1..100 ... printed for comparison, checked by the caller. */
    uint64_t neg = 0;
    for (int64_t M = 1; M <= 20000; M++) {
        double dm = (double) M;
        for (int m = -1000; m <= -1; m++)
            neg += (float) (dm + ((double) m * 0.1)) != (float) fma((double) m, 0.1, dm);
    }
    printf("self-check block (major 1..20000, minor -1000..-1): %llu differing\n", (unsigned long long) neg);
    /* self-check 2: the known out-of-range pair must differ (review round 1: minor=-10*major) */
    volatile double one = 1.0; volatile int mneg = -10;
    int ctl = (float) (one + ((double) mneg * 0.1)) != (float) fma((double) mneg, 0.1, one);
    printf("pairs %llu, differing %llu; control (major=1, minor=-10) differs: %s\n",
           (unsigned long long) pairs, (unsigned long long) bad, ctl ? "yes" : "NO (harness broken)");
    return bad != 0 || !ctl;
}
