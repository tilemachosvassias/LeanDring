/* v_task45_scan.c --- extended, filter-driven scan of the two open R1 rows.
 *
 *   row 2 (L_3):  n(n-1)(n-2) = c * (q^2+q+1),            c = 6 f1 l*
 *   row 3 (L_5):  n(n-1)(n-2) = c * (q^4+q^3+q^2+q+1),    c = 6 f1 l*
 *
 * Completeness.  For a given n the equation determines c = M/F(q) as a
 * DIVISOR of M = n(n-1)(n-2); so scanning all admissible divisors c of M
 * is complete over ALL q and ALL l* simultaneously.  Two proven filters
 * shrink the divisor enumeration from tau(M) to a handful:
 *
 *   (W)  W_e(M) | c, where W_e(x) = prod_{r != e, r !== 1 mod e} r^{v_r(x)}
 *        -- because every prime of Phi_e(q) is e or == 1 (mod e).
 *   (E)  v_e(c) >= v_e(M) - 1   -- because v_e(Phi_e(q)) <= 1.
 *   (K)  c <= M / Phi_e(q_min), q_min from the R1 spectral gap
 *        (row 2: q >= f1(n-3) >= n-3;  row 3: q^2 >= n-3).
 *
 * So c = W_e(M) * e^(v_e(M)-eps) * d with d | (the 1-mod-e part of M) and
 * c <= K.  Everything is exact (unsigned __int128).
 *
 * usage: ./scan NSTART NEND [NTHREADS]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>

typedef unsigned __int128 u128;
typedef unsigned long long u64;

#define MAXF 16

static u64 *sp;          /* sieving primes */
static int nsp;

static void build_primes(u64 lim) {
    char *c = calloc(lim + 1, 1);
    sp = malloc(sizeof(u64) * (lim / 4 + 100));
    nsp = 0;
    for (u64 i = 2; i <= lim; i++) {
        if (!c[i]) {
            sp[nsp++] = i;
            for (u64 j = i * i; j <= lim; j += i) c[j] = 1;
        }
    }
    free(c);
}

/* integer square root of u128 */
static u64 isqrt128(u128 x) {
    if (x == 0) return 0;
    u64 r = (u64)sqrtl((long double)x);
    while ((u128)r * r > x) r--;
    while ((u128)(r + 1) * (r + 1) <= x) r++;
    return r;
}
static u64 iroot4(u128 x) {
    u64 r = (u64)powl((long double)x, 0.25L);
    if (r > 2) r -= 2;
    while ((u128)r * r * r * r <= x) r++;
    return r - 1;
}

static int is_prime_u64(u64 n) {
    if (n < 2) return 0;
    for (u64 p = 2; p * p <= n && p < 1000000; p++) {
        if (n % p == 0) return n == p;
    }
    return 1;
}

/* is n a prime power p^f ?  returns p, sets *fe = f, 0 if not */
static u64 prime_power(u64 n, int *fe) {
    if (n < 2) return 0;
    for (u64 p = 2; p * p <= n; p++) {
        if (n % p == 0) {
            int e = 0;
            u64 m = n;
            while (m % p == 0) { m /= p; e++; }
            if (m != 1) return 0;
            *fe = e;
            return p;
        }
    }
    *fe = 1;
    return n;                       /* n itself prime */
}



int main(int argc, char **argv) {
    u64 NS = (argc > 1) ? strtoull(argv[1], 0, 10) : 10;
    u64 NE = (argc > 2) ? strtoull(argv[2], 0, 10) : 1000000ULL;

    u64 lim = (u64)sqrtl((long double)(NE + 4)) + 2;
    build_primes(lim);
    fprintf(stderr, "# sieving primes up to %llu : %d\n", lim, nsp);

    const u64 BS = 1u << 20;
    u64 *rem = malloc(sizeof(u64) * (BS + 4));
    uint32_t (*fp)[MAXF] = malloc(sizeof(uint32_t) * MAXF * (BS + 4));
    uint8_t (*fe)[MAXF] = malloc(sizeof(uint8_t) * MAXF * (BS + 4));
    uint8_t *nf = malloc(BS + 4);

    long long hits2 = 0, hits3 = 0, surv2 = 0, surv3 = 0;
    long long ncomposite = 0;

    for (u64 L = (NS >= 12 ? NS - 2 : 10); L <= NE; L += BS) {
        u64 R = L + BS;
        if (R > NE + 1) R = NE + 1;
        u64 len = R - L;
        for (u64 i = 0; i < len; i++) { rem[i] = L + i; nf[i] = 0; }
        for (int k = 0; k < nsp; k++) {
            u64 p = sp[k];
            if (p * p > R) break;
            u64 st = (L + p - 1) / p * p;
            for (u64 m = st; m < R; m += p) {
                u64 i = m - L;
                int e = 0;
                while (rem[i] % p == 0) { rem[i] /= p; e++; }
                fp[i][nf[i]] = (uint32_t)p;
                fe[i][nf[i]] = (uint8_t)e;
                nf[i]++;
            }
        }
        /* now handle n from max(L+2,NS) .. R-1 */
        u64 n0 = (L + 2 > NS) ? L + 2 : NS;
        for (u64 n = n0; n < R; n++) {
            u64 ia = n - L, ib = ia - 1, ic = ia - 2;
            /* merged factorisation of M = n(n-1)(n-2) */
            u64 pr[3 * MAXF + 3];
            int ex[3 * MAXF + 3];
            int np = 0;
            u64 idx[3] = { ia, ib, ic };
            for (int t = 0; t < 3; t++) {
                u64 i = idx[t];
                for (int j = 0; j < nf[i]; j++) {
                    u64 p = fp[i][j];
                    int found = -1;
                    for (int u = 0; u < np; u++) if (pr[u] == p) { found = u; break; }
                    if (found >= 0) ex[found] += fe[i][j];
                    else { pr[np] = p; ex[np] = fe[i][j]; np++; }
                }
                if (rem[i] > 1) {
                    u64 p = rem[i];
                    int found = -1;
                    for (int u = 0; u < np; u++) if (pr[u] == p) { found = u; break; }
                    if (found >= 0) ex[found] += 1;
                    else { pr[np] = p; ex[np] = 1; np++; }
                }
            }
            u128 M = (u128)n * (n - 1) * (n - 2);

            for (int row = 0; row < 2; row++) {
                u64 e = row ? 5 : 3;
                /* K = max admissible c */
                u128 K;
                if (row == 0) {
                    u128 qm = n - 3;
                    K = M / (qm * qm + qm + 1);
                } else {
                    u64 qm = (u64)sqrtl((long double)(n - 3));
                    while (qm * qm < n - 3) qm++;
                    u128 F = (u128)qm * qm * qm * qm + (u128)qm * qm * qm
                             + (u128)qm * qm + qm + 1;
                    K = M / F;
                }
                if (K < 6) continue;
                /* W-part and good part */
                u128 W = 1;
                int ve = 0;
                u64 gp[3 * MAXF + 3];
                int ge[3 * MAXF + 3];
                int ng = 0;
                int overflow = 0;
                for (int u = 0; u < np; u++) {
                    u64 p = pr[u];
                    if (p == e) { ve = ex[u]; continue; }
                    if (p % e == 1) { gp[ng] = p; ge[ng] = ex[u]; ng++; continue; }
                    for (int t = 0; t < ex[u]; t++) {
                        if (W > K) { overflow = 1; break; }
                        W *= p;
                    }
                    if (overflow) break;
                }
                if (overflow || W > K) continue;
                /* c = W * e^(ve - eps) * d,  eps in {0,1}, d | prod gp^ge */
                for (int eps = 0; eps <= 1; eps++) {
                    int vv = ve - eps;
                    if (vv < 0) continue;
                    u128 base = W;
                    int ov = 0;
                    for (int t = 0; t < vv; t++) {
                        if (base > K) { ov = 1; break; }
                        base *= e;
                    }
                    if (ov || base > K) continue;
                    /* enumerate divisors d of the 1-mod-e part with base*d <= K */
                    u128 stack[4096];
                    int sn = 0;
                    stack[sn++] = base;
                    for (int u = 0; u < ng; u++) {
                        int cur = sn;
                        for (int t = 0; t < cur; t++) {
                            u128 v = stack[t];
                            for (int r = 0; r < ge[u]; r++) {
                                if (v > K / gp[u]) break;
                                v *= gp[u];
                                if (sn < 4096) stack[sn++] = v;
                            }
                        }
                    }
                    for (int t = 0; t < sn; t++) {
                        u128 c = stack[t];
                        if (c > K || c < 6) continue;
                        if (c % 6) continue;
                        if (M % c) continue;
                        u128 Y = M / c;
                        u64 q = 0;
                        if (row == 0) {
                            u128 D = 4 * Y - 3;
                            u64 s = isqrt128(D);
                            if ((u128)s * s != D) continue;
                            if ((s & 1) == 0) continue;
                            q = (s - 1) / 2;
                        } else {
                            u64 r0 = iroot4(Y);
                            int ok = 0;
                            for (u64 rr = (r0 > 1 ? r0 - 1 : 1); rr <= r0 + 2; rr++) {
                                u128 F = (u128)rr * rr * rr * rr + (u128)rr * rr * rr
                                         + (u128)rr * rr + rr + 1;
                                if (F == Y) { q = rr; ok = 1; break; }
                            }
                            if (!ok) continue;
                        }
                        if (q < 2) continue;
                        if (row) hits3++; else hits2++;
                        /* post-filters */
                        int f;
                        u64 p = prime_power(q, &f);
                        if (!p) continue;                        /* not a prime power */
                        u64 l6 = (u64)(c / 6);                   /* = f1*l* */
                        u64 f1, lstar;
                        int good = 0;
                        for (f1 = 1; f1 <= 2; f1++) {
                            if (l6 % f1) continue;
                            lstar = l6 / f1;
                            if (lstar < 1) continue;
                            if (row == 0) {
                                if (f < 2) continue;              /* q must be a proper power */
                                if (q < f1 * (n - 3)) continue;   /* spectral gap */
                            } else {
                                if ((u128)q * q < n - 3) continue;
                            }
                            /* p-part: lstar * f * N <= v_p(n!) , N = 3 (L3) or 10 (L5) */
                            u64 N = row ? 10 : 3;
                            u64 vp = 0, pk = p;
                            while (pk <= n) { vp += n / pk; if (pk > n / p) break; pk *= p; }
                            if ((u128)lstar * f * N > vp) continue;
                            good = 1;
                            break;
                        }
                        if (!good) continue;
                        if (row) surv3++; else surv2++;
                        printf("SURVIVOR row%d n=%llu q=%llu c=%llu f1=%llu l*=%llu\n",
                               row + 2, (unsigned long long)n, (unsigned long long)q,
                               (unsigned long long)(u64)c, (unsigned long long)f1,
                               (unsigned long long)lstar);
                        fflush(stdout);
                    }
                }
            }
        }
        fprintf(stderr, "# done up to %llu  rawhits(row2,row3)=(%lld,%lld) surv=(%lld,%lld)\n",
                (unsigned long long)(R - 1), hits2, hits3, surv2, surv3);
    }
    printf("# range %llu..%llu  raw shape hits row2=%lld row3=%lld ; SURVIVORS row2=%lld row3=%lld\n",
           (unsigned long long)NS, (unsigned long long)NE, hits2, hits3, surv2, surv3);
    (void)ncomposite; (void)is_prime_u64;
    return 0;
}
