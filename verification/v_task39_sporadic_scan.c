/* v_task39_sporadic_scan.c -- the sporadic row of Theorem AT, run to
 * exhaustion with the EXACT iota values of v_task39_sporadic_iota.g.
 *
 * A twin T of A_n with a sporadic socle factor S (orbit length l, induced
 * almost simple pair K <= Abar) fails to be separated by kappa only if
 *      l * v = C(n,3),        v = iota(K <= Abar),
 * (Lemma TR-1 / v_task34: iota(T) <= min over orbits of l_O*iota_O, and
 * separation holds as soon as iota(T) != C(n,3) = iota(A_n)).
 * By Lemma F (v_task36) v = f(A)*[S:N_S(A)] with f | |Out S|; for sporadics
 * |Out S| <= 2, so v in V(S) := { m*w : w in I(S), w <= 2*iota(S),
 * m = 1..|Out S| } and v <= 2*iota(S).  V(S) is taken from the exact
 * maximal-normalizer spectrum computed by v_task39_sporadic_iota.g.
 *
 * Side conditions (necessary for T to exist at all, with |T| = n!/2):
 *   (TO-2)  l * log|S| <= log(n!/2)              [order squeeze, v_task36 err.1]
 *   (pp)    l * v_p(|S|) <= v_p(n!) for all p    [p-part of |S|^l | n!/2]
 *
 * The scan is complete in l: for each S and v it runs every l >= 1 for which
 * (TO-2) can hold, i.e. the whole n-range up to each group's reach.
 *
 * Compile: cc -O2 -o scan v_task39_sporadic_scan.c -lm
 */
#include <stdio.h>
#include <math.h>
#include <string.h>

typedef __int128 i128;

typedef struct { int p, a; } PF;
typedef struct {
  const char *name;
  double logord;      /* log |S| */
  int nout;           /* |Out S| */
  PF f[16]; int nf;   /* factorisation of |S| */
  long long va[12], vb[12]; int nv;  /* candidate values V(S) = va*vb */
} Grp;

static Grp G[] = {
#define E {0,0}
 {"M11",   log(7920.0),1,{{2,4},{3,2},{5,1},{11,1}},4,{55LL},{1},1},
 {"M12",   log(95040.0),2,{{2,6},{3,3},{5,1},{11,1}},4,{220LL,396LL,440LL,792LL},{1,1,1,1},4},
 {"M22",   log(443520.0),2,{{2,7},{3,2},{5,1},{7,1},{11,1}},5,{77LL,154LL},{1,1},2},
 {"M23",   log(10200960.0),1,{{2,7},{3,2},{5,1},{7,1},{11,1},{23,1}},6,{253LL},{1},1},
 {"M24",   log(244823040.0),1,{{2,10},{3,3},{5,1},{7,1},{11,1},{23,1}},6,{759LL},{1},1},
 {"J1",    log(175560.0),1,{{2,3},{3,1},{5,1},{7,1},{11,1},{19,1}},6,{1045LL},{1},1},
 {"J2",    log(604800.0),2,{{2,7},{3,3},{5,2},{7,1}},4,{280LL,315LL,525LL,560LL},{1,1,1,1},4},
 {"J3",    log(50232960.0),2,{{2,7},{3,5},{5,1},{17,1},{19,1}},5,
           {17442LL,23256LL,25840LL,26163LL,34884LL},{1,1,1,1,1},5},
 {"HS",    log(44352000.0),2,{{2,9},{3,2},{5,3},{7,1},{11,1}},5,
           {3850LL,4125LL,5775LL,7700LL},{1,1,1,1},4},
 {"McL",   log(898128000.0),2,{{2,7},{3,6},{5,3},{7,1},{11,1}},5,
           {15400LL,22275LL,30800LL},{1,1,1},3},
 {"He",    log(4030387200.0),2,{{2,10},{3,3},{5,2},{7,3},{17,1}},5,{8330LL,16660LL},{1,1},2},
 {"Ru",    log(145926144000.0),1,{{2,14},{3,3},{5,3},{7,1},{13,1},{29,1}},6,{188500LL},{1},1},
 {"Suz",   log(448345497600.0),2,{{2,13},{3,7},{5,2},{7,1},{11,1},{13,1}},6,
           {22880LL,45760LL},{1,1},2},
 {"Co1",   log(4157776806543360000.0),1,
           {{2,21},{3,9},{5,4},{7,2},{11,1},{13,1},{23,1}},7,{1545600LL},{1},1},
 {"Co2",   log(42305421312000.0),1,{{2,18},{3,6},{5,3},{7,1},{11,1},{23,1}},6,{46575LL},{1},1},
 {"Co3",   log(495766656000.0),1,{{2,10},{3,7},{5,3},{7,1},{11,1},{23,1}},6,{128800LL},{1},1},
 {"Fi22",  log(64561751654400.0),2,{{2,17},{3,9},{5,2},{7,1},{11,1},{13,1}},6,
           {3510LL,7020LL},{1,1},2},
 {"Fi23",  log(4089470473293004800.0),1,
           {{2,18},{3,13},{5,2},{7,1},{11,1},{13,1},{17,1},{23,1}},8,{31671LL},{1},1},
 {"Fi24'", 1255205709190661721292800.0>0?log(1.2552057091906617e24):0,2,
           {{2,21},{3,16},{5,2},{7,3},{11,1},{13,1},{17,1},{23,1},{29,1}},9,
           {4860485028LL,9720970056LL},{1,1},2},
 {"HN",    log(2.73030912e14),2,{{2,14},{3,6},{5,6},{7,1},{11,1},{19,1}},6,
           {1539000LL,3078000LL},{1,1},2},
 {"Th",    log(9.0745943887872e16),1,
           {{2,15},{3,10},{5,3},{7,2},{13,1},{19,1},{31,1}},7,{283599225LL},{1},1},
 {"ON",    log(4.6081550592e11),2,{{2,9},{3,4},{5,1},{7,3},{11,1},{19,1},{31,1}},7,
           {2857239LL,5714478LL},{1,1},2},
 {"Ly",    log(5.1765179004e16),1,
           {{2,8},{3,7},{5,6},{7,1},{11,1},{31,1},{37,1},{67,1}},8,{9606125LL},{1},1},
 {"J4",    log(8.677557104607756e19),1,
           {{2,21},{3,3},{5,1},{7,1},{11,3},{23,1},{29,1},{31,1},{37,1},{43,1}},10,
           {173067389LL},{1},1},
 {"B",     log(4.154781481226426e33),1,
           {{2,41},{3,13},{5,6},{7,2},{11,1},{13,1},{17,1},{19,1},{23,1},{31,1},{47,1}},11,
           {13571955000LL},{1},1},
 {"M",     log(8.080174247945128e53),1,
           {{2,46},{3,20},{5,9},{7,6},{11,2},{13,3},{17,1},{19,1},{23,1},{29,1},
            {31,1},{41,1},{47,1},{59,1},{71,1}},15,{100LL},{972394611420091860LL},1},
 {"2F4(2)'",log(17971200.0),2,{{2,11},{3,3},{5,2},{13,1}},4,{1755LL,2925LL,3510LL},{1,1,1},3},
};
static const int NG = sizeof(G)/sizeof(G[0]);

/* log(n!/2) */
static double lfac2(double n){ return lgamma(n+1.0) - log(2.0); }

/* v_p(n!) */
static long long vpfact(long long n, long long p){
  long long v=0, q=p;
  while (q<=n){ v += n/q; if (q > n/p) break; q*=p; }
  return v;
}

/* exact integer n with n(n-1)(n-2)=P, or 0 */
static long long cubroot3(i128 P){
  double d = (double)(long long)(P>>64) * 18446744073709551616.0
           + (double)(unsigned long long)(P & (i128)0xFFFFFFFFFFFFFFFFULL);
  long long n = (long long)cbrt(d);
  for (long long c=n-3; c<=n+3; c++){
    if (c<3) continue;
    i128 t = (i128)c*(c-1); t*=(c-2);
    if (t==P) return c;
  }
  return 0;
}

int main(void){
  printf("=== v_task39: exact sporadic iota-coincidence scan ===\n");
  printf("equation  l*v = C(n,3),  v in V(S) (exact spectrum, v <= 2*iota),\n");
  printf("filters   TO-2 order squeeze  +  p-part of |S|^l | n!/2\n\n");
  int live=0, killed=0;
  for (int g=0; g<NG; g++){
    Grp *S = &G[g];
    for (int k=0; k<S->nv; k++){
      i128 v = (i128)S->va[k] * (i128)S->vb[k];
      double vd = (double)S->va[k] * (double)S->vb[k];
      /* find lmax: largest l with l*log|S| <= log(n(l)!/2) */
      long long lmax = 1;
      for (long long l=1; l<(long long)4e12; l = (l<64? l+1 : l + l/8)){
        double n = cbrt(6.0*(double)l*vd);
        if (n<3) n=3;
        if (lfac2(n) >= l*S->logord) lmax = l;
      }
      lmax = lmax + lmax/4 + 16;
      for (long long l=1; l<=lmax; l++){
        i128 P = (i128)6*(i128)l*v;
        long long n = cubroot3(P);
        if (!n || n<5) continue;
        if (lfac2((double)n) < l*S->logord) continue;   /* TO-2 */
        const char *bad = NULL; int badp=0;
        for (int i=0;i<S->nf;i++){
          if (l*(long long)S->f[i].a > vpfact(n, S->f[i].p)){
            bad="p-part"; badp=S->f[i].p; break; }
        }
        if (bad){
          printf("  %-8s v=%-22.0f l=%-12lld n=%-12lld KILLED by p-part at p=%d\n",
                 S->name, vd, l, n, badp);
          killed++;
        } else {
          printf("  %-8s v=%-22.0f l=%-12lld n=%-12lld *** LIVE COINCIDENCE ***\n",
                 S->name, vd, l, n);
          live++;
        }
      }
    }
  }
  printf("\n  live coincidences: %d   (killed by p-part: %d)\n\n", live, killed);

  printf("=== reach: largest n admitting this sporadic as a socle factor ===\n");
  printf("(needs l*2*iota >= C(n,3) for the orbit AND l*log|S| <= log(n!/2))\n");
  long long worst=0; const char *wn="";
  for (int g=0; g<NG; g++){
    Grp *S=&G[g];
    i128 io = (i128)S->va[0] * (i128)S->vb[0];   /* v[0] = iota(S) */
    double iod = (double)S->va[0] * (double)S->vb[0];
    long long best=0;
    for (long long n=5; n<(long long)6e10; n = (n<400? n+1 : n + n/64 + 1)){
      double L = lfac2((double)n)/S->logord;
      if (L < 1) continue;
      long long l = (long long)L;
      i128 lhs = (i128)l * (i128)S->nout * io;
      i128 rhs = (i128)n*(n-1); rhs = rhs*(n-2)/6;
      if (lhs >= rhs) best = n;
    }
    printf("  %-8s iota=%-22.0f  reach n <= %lld\n", S->name, iod, best);
    if (best>worst){ worst=best; wn=S->name; }
  }
  printf("  WORST: %s -- no sporadic socle factor once n > %lld\n", wn, worst);
  return 0;
}
