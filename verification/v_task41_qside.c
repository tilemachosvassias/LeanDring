/* v_task41_qside.c  --  q-side scan of the R1 residue at ell* = 1.
 *
 * Context: v_task38 PART 1.  In residue R1 the ell-minimal orbit satisfies
 *     ell* * f1 * iota1(S*) = C(n,3),
 * and at ell* = 1 this is exactly the equation of NOTES.md 4ao with m = f1.
 * This programme scans the SURVIVING rows from the q-side (complete over all
 * n for each q), which is far cheaper than the n-side scan of v_task38.
 *
 * Rows scanned:
 *   S4(q), q odd, NON-PRIME (f >= 2), f1 = 1 (no graph automorphism at odd q):
 *        (q+1)(q^2+1) = C(n,3),  window (n-1)/2 < q  ==>  n <= 2q.
 *        [Lemma R1-S4-ell1 of v_task41: here ell* = 1 is FORCED.]
 *   L5(q), any prime power, f1 in {1,2}:
 *        f1*(q^5-1)/(q-1) = C(n,3),  window q^2 >= n-3.
 *   L3(q), q non-prime, f1 in {1,2}  (control: proven empty by 4ao + Thm L3_2):
 *        f1*(q^2+q+1) = C(n,3),  window q >= f1*(n-3).
 *
 * All arithmetic in unsigned __int128; the cube root is only a seed and every
 * hit is verified exactly.  Additional filters applied to any hit:
 *   p-PART : f*N <= v_p(n!)  (N = #positive roots: L3 3, L5 10, S4 4)
 *   window : as above.
 *
 * usage: ./qside <QMAX_S4> <QMAX_L5> <QMAX_L3>
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

typedef unsigned __int128 u128;

static unsigned char *sieve;      /* sieve[i]=1 iff 2i+1 composite */
static long SLIM;

static int isprime(long x){
  if(x<2) return 0;
  if(x==2) return 1;
  if(!(x&1)) return 0;
  return !sieve[x>>1];
}
static void build(long lim){
  long i,j;
  SLIM=lim; sieve=calloc(lim/2+1,1);
  for(i=3;i*i<=lim;i+=2) if(!sieve[i>>1])
    for(j=i*i;j<=lim;j+=2*i) sieve[j>>1]=1;
}

/* v_p(n!) by Legendre, n up to ~4e12 */
static long vpfact(long n, long p){
  long v=0; u128 q=p;
  while(q<=(u128)n){ v += (long)(n/(long)q); if(q > (u128)n/p) break; q*=p; }
  return v;
}

/* solve n(n-1)(n-2) = D exactly; return n or 0 */
static long solve_cubic(u128 D){
  long double d = 0.0L; u128 t=D;
  /* convert u128 -> long double */
  d = (long double)(unsigned long long)(t>>64) * 18446744073709551616.0L
    + (long double)(unsigned long long)(t & 0xFFFFFFFFFFFFFFFFULL);
  long r = (long)cbrtl(d);
  for(long n=r-3;n<=r+3;n++){
    if(n<3) continue;
    u128 v=(u128)n*(u128)(n-1)*(u128)(n-2);
    if(v==D) return n;
  }
  return 0;
}

static long hits=0, survivors=0;

static void report(const char*fam,long p,long f,u128 q,long f1,long n,long N,int win_ok){
  hits++;
  long vp = vpfact(n,p);
  int ppart_ok = (f*N <= vp);
  printf("HIT  %s q=%llu (p=%ld,f=%ld) f1=%ld n=%ld  window=%s p-part=%s (f*N=%ld, v_p(n!)=%ld)\n",
     fam,(unsigned long long)q,p,f,f1,n, win_ok?"OK":"FAIL", ppart_ok?"OK":"FAIL", f*N, vp);
  if(win_ok && ppart_ok) survivors++;
}

int main(int argc,char**argv){
  u128 QS4 = argc>1? (u128)strtoull(argv[1],0,10) : (u128)1000000000000ULL;
  u128 QL5 = argc>2? (u128)strtoull(argv[2],0,10) : (u128)100000000ULL;
  u128 QL3 = argc>3? (u128)strtoull(argv[3],0,10) : (u128)1000000000000ULL;

  u128 mx = QS4>QL5?QS4:QL5; if(QL3>mx) mx=QL3;
  /* primes needed: up to QL5 (L5 allows f=1); for f>=2 rows only sqrt */
  long plim = (long)QL5;
  long s4lim = (long)sqrtl((long double)QS4)+2;
  long l3lim = (long)sqrtl((long double)QL3)+2;
  if(s4lim>plim) plim=s4lim; if(l3lim>plim) plim=l3lim;
  fprintf(stderr,"sieving to %ld\n",plim);
  build(plim);

  /* positive control for solve_cubic: 6*C(14,3)=2184=14*13*12; and a huge one */
  {
    long n0 = solve_cubic((u128)2184);
    long n1 = solve_cubic((u128)1000000000001ULL*(u128)1000000000000ULL*(u128)999999999999ULL);
    printf("# selftest solve_cubic: 2184 -> %ld (expect 14); 1e12-scale -> %ld (expect 1000000000001)\n",n0,n1);
  }
  printf("# v_task41 q-side scan of R1 at ell*=1\n");
  printf("# S4 (odd non-prime q) q <= %llu ; L5 q <= %llu ; L3 (non-prime q) q <= %llu\n",
     (unsigned long long)QS4,(unsigned long long)QL5,(unsigned long long)QL3);

  for(long p=2;p<=plim;p++){
    if(!isprime(p)) continue;
    u128 q=(u128)p; long f=1;
    while(1){
      /* ---- L5 : all prime powers, f1 = 1,2 ---- */
      if(q<=QL5){
        u128 i1 = (((q*q*q*q)+(q*q*q))+(q*q))+q+1;   /* q^4+q^3+q^2+q+1 */
        for(long f1=1;f1<=2;f1++){
          u128 D = 6*(u128)f1*i1;
          long n = solve_cubic(D);
          if(n) report("L5",p,f,q,f1,n,10, (q*q >= (u128)(n-3)));
        }
      }
      /* ---- S4 : q odd, f>=2, f1=1 ---- */
      if(p!=2 && f>=2 && q<=QS4){
        u128 i1 = (q+1)*(q*q+1);
        u128 D = 6*i1;
        long n = solve_cubic(D);
        if(n) report("S4",p,f,q,1,n,4, ((u128)(n-1) < 2*q));
      }
      /* ---- L3 : f>=2, f1=1,2 (control) ---- */
      if(f>=2 && q<=QL3){
        u128 i1 = q*q+q+1;
        for(long f1=1;f1<=2;f1++){
          u128 D = 6*(u128)f1*i1;
          long n = solve_cubic(D);
          if(n) report("L3",p,f,q,f1,n,3, (q >= (u128)f1*(u128)(n-3)));
        }
      }
      if(q > mx/(u128)p) break;
      q*=(u128)p; f++;
      if(q>mx) break;
    }
  }
  printf("# raw shape hits: %ld\n# SURVIVORS (window + p-part): %ld\n",hits,survivors);
  return 0;
}
