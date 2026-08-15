/* v_task27_lastmile_scan.c  --- the eight residual equations of NOTES.md
 * Sec.4ao, scanned from the CHEAP side with exact 128-bit arithmetic.
 *
 *   equation:   m * iota_F(q) = C(n,3),  m in {1,2}
 *   normalised: 6*m*f(q) = n(n-1)(n-2) = k^3 - k,   k = n-1.
 *
 * For deg f >= 3 we scan q (then k ~ n follows monotonically, so the cube
 * test is an amortised O(1) increment -- no floating point anywhere).
 * For deg f = 2 the q-side is the expensive one (q ~ n^{3/2}), so we scan n
 * and test whether 4X-3 is a square, X = k(k^2-1)/(6m).
 *
 * Build:  gcc -O3 -march=native -fopenmp -o scan v_task27_lastmile_scan.c -lm
 * Usage:  ./scan <NMAX>            (bound on n; every equation is covered
 *                                   for 3 <= n <= NMAX)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <omp.h>

typedef __int128 i128;
typedef unsigned __int128 u128;

static void print_u128(u128 v, char *buf) {           /* buf >= 44 bytes */
    char tmp[44]; int i = 0;
    if (v == 0) { strcpy(buf, "0"); return; }
    while (v) { tmp[i++] = '0' + (int)(v % 10); v /= 10; }
    int j = 0; while (i) buf[j++] = tmp[--i];
    buf[j] = 0;
}

/* ---- the eight polynomials f(q), by exponent list ---------------------- */
typedef struct { const char *name; int exps[8]; int nexp; int mult; int deg; }
        Eq;

static Eq EQS[] = {
  {"S4/L4  m=1", {3,2,1,0},       4, 1, 3},   /* q^3+q^2+q+1              */
  {"U4     m=1", {4,3,1,0},       4, 1, 4},   /* q^4+q^3+q+1              */
  {"L5     m=1", {4,3,2,1,0},     5, 1, 4},   /* q^4+q^3+q^2+q+1          */
  {"G2/Sp6 m=1", {5,4,3,2,1,0},   6, 1, 5},   /* q^5+...+1                */
  {"U5     m=1", {7,5,2,0},       4, 1, 7},   /* q^7+q^5+q^2+1            */
  {"L3     m=2", {2,1,0},         3, 2, 2},   /* 2(q^2+q+1)               */
  {"L4     m=2", {3,2,1,0},       4, 2, 3},   /* 2(q^3+q^2+q+1)           */
  {"L5     m=2", {4,3,2,1,0},     5, 2, 4},   /* 2(q^4+q^3+q^2+q+1)       */
};
#define NEQ ((int)(sizeof(EQS)/sizeof(EQS[0])))

static u128 fpoly(const Eq *e, u128 q) {
    u128 s = 0;
    for (int i = 0; i < e->nexp; i++) {
        u128 t = 1;
        for (int j = 0; j < e->exps[i]; j++) t *= q;
        s += t;
    }
    return s;
}

/* cube-root floor of a u128, via long double then exact correction */
static u128 icbrt(u128 v) {
    long double x = (long double)v;
    u128 r = (u128)cbrtl(x);
    if (r > 4) r -= 4; else r = 0;
    while ((r + 1) <= (u128)-1 && (r + 1) * (r + 1) * (r + 1) <= v) r++;
    return r;
}
static u128 isqrt128(u128 v) {
    long double x = (long double)v;
    u128 r = (u128)sqrtl(x);
    if (r > 4) r -= 4; else r = 0;
    while ((r + 1) * (r + 1) <= v) r++;
    return r;
}

/* squares bitmap mod 2^16, to pre-filter the deg-2 sweep */
static unsigned char sqmask[1 << 13];
static void build_sqmask(void) {
    for (unsigned i = 0; i < (1u << 16); i++) {
        unsigned r = (unsigned)((1ull * i * i) & 0xffffu);
        sqmask[r >> 3] |= (unsigned char)(1u << (r & 7));
    }
}

static long long NMAX;
static long hits_total = 0;

/* ---- deg >= 3: scan q, keep a running k with k^3-k <= T --------------- */
static void scan_q(const Eq *e) {
    u128 kcap = (u128)NMAX - 1;                 /* k = n-1 <= NMAX-1      */
    u128 Tcap = kcap * kcap * kcap - kcap;
    /* largest q with 6*mult*f(q) <= Tcap */
    u128 qmax = 1;
    while (6 * (u128)e->mult * fpoly(e, qmax * 2) <= Tcap) qmax *= 2;
    { u128 lo = qmax, hi = qmax * 2;
      while (lo + 1 < hi) { u128 mid = lo + (hi - lo) / 2;
        if (6 * (u128)e->mult * fpoly(e, mid) <= Tcap) lo = mid; else hi = mid; }
      qmax = lo; }

    long hits = 0;
    u128 span = (qmax >= 2) ? (qmax - 1) : 0;   /* q runs over 2..qmax    */
    long long chunks = 4096;
    if ((u128)chunks > span) chunks = (long long)span;
    if (chunks < 1) chunks = 1;
    #pragma omp parallel for schedule(dynamic) reduction(+:hits)
    for (long long c = 0; c < chunks; c++) {
        u128 qlo = 2 + span * (u128)c / (u128)chunks;
        u128 qhi = 2 + span * (u128)(c + 1) / (u128)chunks - 1;
        if (c == chunks - 1) qhi = qmax;
        if (qlo > qhi) continue;
        u128 T = 6 * (u128)e->mult * fpoly(e, qlo);
        u128 k = icbrt(T);
        while (k > 1 && k * k * k - k > T) k--;
        for (u128 q = qlo; q <= qhi; q++) {
            T = 6 * (u128)e->mult * fpoly(e, q);
            while ((k + 1) * (k + 1) * (k + 1) - (k + 1) <= T) k++;
            if (k * k * k - k == T) {
                char b1[44], b2[44];
                print_u128(q, b1); print_u128(k + 1, b2);
                #pragma omp critical
                printf("  HIT  %s   q = %s   n = %s\n", e->name, b1, b2);
                hits++;
            }
        }
    }
    printf("  %-12s scanned q = 2 .. %.6Lg  (covers n <= %lld)   hits: %ld\n",
           e->name, (long double)qmax, NMAX, hits);
    #pragma omp atomic
    hits_total += hits;
}

/* ---- deg 2: scan n, test that 4X-3 is a perfect square ---------------- */
static void scan_n(const Eq *e) {
    u128 d = 6 * (u128)e->mult;                 /* = 12 for L3 m=2        */
    long hits = 0;
    #pragma omp parallel for schedule(static) reduction(+:hits)
    for (long long n = 3; n <= NMAX; n++) {
        u128 k = (u128)n - 1;
        u128 T = k * k * k - k;                 /* = n(n-1)(n-2)          */
        if (T % d) continue;
        u128 X = T / d;                         /* must equal q^2+q+1     */
        u128 W = 4 * X - 3;                     /* = (2q+1)^2             */
        unsigned r = (unsigned)(W & 0xffffu);
        if (!(sqmask[r >> 3] & (1u << (r & 7)))) continue;
        u128 s = isqrt128(W);
        if (s * s == W) {
            char b1[44], b2[44];
            print_u128((s - 1) / 2, b1); print_u128((u128)n, b2);
            #pragma omp critical
            printf("  HIT  %s   q = %s   n = %s\n", e->name, b1, b2);
            hits++;
        }
    }
    printf("  %-12s scanned n = 3 .. %lld                          hits: %ld\n",
           e->name, NMAX, hits);
    #pragma omp atomic
    hits_total += hits;
}

int main(int argc, char **argv) {
    NMAX = (argc > 1) ? atoll(argv[1]) : 1000000LL;
    build_sqmask();
    printf("v_task27: residual last-mile equations, n <= %lld, %d threads\n",
           NMAX, omp_get_max_threads());
    printf("(all integer q >= 2 are scanned -- prime-power / |S| divisibility\n"
           " filters are applied afterwards to any hit)\n\n");
    for (int i = 0; i < NEQ; i++) {
        double t0 = omp_get_wtime();
        if (EQS[i].deg >= 3) scan_q(&EQS[i]); else scan_n(&EQS[i]);
        printf("       %.1f s\n", omp_get_wtime() - t0);
        fflush(stdout);
    }
    printf("\nTOTAL HITS: %ld\n", hits_total);
    return 0;
}
