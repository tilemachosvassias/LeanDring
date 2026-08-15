/* v_task84 -- independent brute-force enumeration of the integral points of
 *   C_c : k^3 - k = c(q^2+q+1)      (the row-2 locus, NOT the ambient E_c)
 * for every admissible c = 6*f1*ell* <= CMAX, over |k| <= KMAX.  Used to
 * re-derive v_task46's table (its "witness (k,q)" column) without Sage, and to
 * measure how log|4ck| grows with log c -- the quantity Theorem U needs.
 *
 * cc -O2 -o ccscan v_task84_ccscan.c -lm ; ./ccscan 216 20000000              */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef __int128 i128;
typedef long long ll;

static ll isqrtll(ll n){ if(n<0) return -1; ll r=(ll)sqrtl((long double)n);
  while(r>0 && r*r>n) r--; while((r+1)*(r+1)<=n) r++; return r; }

int main(int argc,char**argv){
  ll CMAX = argc>1?atoll(argv[1]):216;
  ll KMAX = argc>2?atoll(argv[2]):2000000;
  printf("# c   #pts_on_C_c   max log|4ck|   witness(k,q)   2logc+log2   ratio logX/logc\n");
  for(ll c=6;c<=CMAX;c+=6){
    ll best=-1,bk=0,bq=0; int cnt=0;
    for(ll k=-KMAX;k<=KMAX;k++){
      i128 m = (i128)k*k*k - k;
      if(m<0) continue;                  /* q^2+q+1 > 0 always */
      if(m % c) continue;
      i128 t = m/c;                      /* need t = q^2+q+1, q integer       */
      i128 D = 4*t-3;                    /* q = (-1 + sqrt(4t-3))/2           */
      if(D<0) continue;
      if(D > (i128)9e36) continue;
      /* integer sqrt of D (128-bit) */
      long double dd=(long double)D; ll r=(ll)sqrtl(dd);
      while(r>0 && (i128)r*r>D) r--; while((i128)(r+1)*(r+1)<=D) r++;
      if((i128)r*r!=D) continue;
      if(((r-1)&1)) continue;
      ll q=(r-1)/2;
      if((i128)q*q+q+1 != t) continue;
      cnt++;
      ll X = 4*c*(k<0?-k:k);
      if(X>best){best=X;bk=k;bq=q;}
    }
    if(cnt){
      double lx = best>0?log((double)best):0;
      printf("%-5lld %-6d %12.4f   (%lld,%lld)   %8.4f   %6.3f%s\n",
             c,cnt,lx,bk,bq,2*log((double)c)+log(2.0),
             lx/log((double)c),
             lx > 2*log((double)c)+log(2.0) ? "   THRESHOLD-1 VIOLATED":"");
    }
  }
  return 0;
}
