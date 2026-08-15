/* v_task42_r1_weakgap.c (derived from v_task38_r1_scan.c) -- exact, COMPLETE scan closing residue R1 of
 * verify/v_task37_two_orbit.md for every n in [10, NMAX].
 *
 * R1 (v_task37 Thm, case (b) final form).  T Fitting-free, |T| = n!/2,
 * D(T) = D(A_n), n >= 10, >= 3 socle orbits, and on the iota-minimal orbit O*
 *
 *      l* . a1 = C(n,3),   a1 = iota(K<=Abar)_{O*},   a2/a1 > n-3.
 *
 * With the pair table of v_task36 s3-s4 (a1 = f1*iota1(S), a2/a1 = R^p) the
 * necessary conditions on (family F, q, f1, l*, n) are
 *
 *   (1) GAP    R^p(F,q,f1) > n-3
 *   (2) DIV    l* * f1 * iota1(q) = C(n,3),  l* >= 1 integer
 *   (3) SIZE   |S| > C(n,4)                    [v_task37 Step 1; uses (*)]
 *   (4) pPART  l* * f * N <= v_p(n!)           [ |S|_p = q^N, q = p^f ]
 *   (5) ORDER  l* * log|S| <= log(n!/2)        [Lemma TO-2]
 *
 * Search: loop over n; enumerate the divisors l of C(n,3) with l <= n/6 + 3
 * (Lemma L-bound of the write-up: (1) forces iota1 >= (n-3)^2 in every
 * residual family, hence l* = C(n,3)/(f1 iota1) <= n/6 + 3);  put
 * D = C(n,3)/l = f1*iota1 and solve each family's shape equation for q
 * EXACTLY.  Every q is therefore covered, however large: the scan is
 * complete in q for each n, not merely over a q-range.
 *
 * Build: gcc -O2 -o /tmp/r1 v_task38_r1_scan.c -lm
 * Run:   /tmp/r1 20000000
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

typedef unsigned long long u64;
typedef __int128 i128;
typedef unsigned __int128 u128;

static int *spf;
static long long NMAX;
static long long nsurv=0, ngapwin=0, nshape=0; static long long shf[8]={0};

/* ---------------- deterministic Miller-Rabin ---------------- */
static const u64 MRB[12]={2,3,5,7,11,13,17,19,23,29,31,37};
static u64 mulmod(u64 a,u64 b,u64 m){ return (u64)((u128)a*b%m); }
static u64 powmod(u64 a,u64 e,u64 m){ u64 r=1;a%=m; while(e){ if(e&1)r=mulmod(r,a,m); a=mulmod(a,a,m); e>>=1;} return r; }
static int isprime(u64 n){
    if(n<2)return 0;
    for(int i=0;i<12;i++){ if(n%MRB[i]==0) return n==MRB[i]; }
    u64 d=n-1; int s=0; while(!(d&1)){d>>=1;s++;}
    for(int i=0;i<12;i++){
        u64 x=powmod(MRB[i],d,n); if(x==1||x==n-1) continue;
        int ok=0; for(int j=1;j<s;j++){ x=mulmod(x,x,n); if(x==n-1){ok=1;break;} }
        if(!ok) return 0;
    }
    return 1;
}
static int prime_power(u64 q,u64*pp){          /* returns f, q=p^f, else 0 */
    if(q<2) return 0;
    if(isprime(q)){ *pp=q; return 1; }
    for(int k=2;k<=63;k++){
        double r=pow((double)q,1.0/k); u64 b=(u64)(r+0.5); if(b<2) break;
        for(u64 c=(b>2?b-2:2); c<=b+2; c++){
            u128 v=1; int of=0;
            for(int i=0;i<k;i++){ v*=c; if(v>(u128)q){of=1;break;} }
            if(!of && v==(u128)q && isprime(c)){ *pp=c; return k; }
        }
    }
    return 0;
}
static long long vp_fact(long long n,u64 p){
    long long v=0; u64 pk=p;
    while((long long)pk<=n){ v += n/(long long)pk; if(pk > (u64)n/p) break; pk*=p; }
    return v;
}
static double logS_lie(double q,const char*fam){
    double lq=log(q);
    if(!strcmp(fam,"L3"))  return 8*lq+log1p(-pow(q,-3))+log1p(-pow(q,-2))-log(3.0);
    if(!strcmp(fam,"L4"))  return 15*lq+log1p(-pow(q,-2))+log1p(-pow(q,-3))+log1p(-pow(q,-4))-log(4.0);
    if(!strcmp(fam,"L5"))  return 24*lq+log1p(-pow(q,-2))+log1p(-pow(q,-3))+log1p(-pow(q,-4))+log1p(-pow(q,-5))-log(5.0);
    if(!strcmp(fam,"U4"))  return 15*lq+log1p(-pow(q,-2))+log1p(pow(q,-3))+log1p(-pow(q,-4))-log(4.0);
    if(!strcmp(fam,"S4"))  return 10*lq+log1p(-pow(q,-2))+log1p(-pow(q,-4))-log(2.0);
    if(!strcmp(fam,"Sp6")) return 21*lq+log1p(-pow(q,-2))+log1p(-pow(q,-4))+log1p(-pow(q,-6))-log(2.0);
    if(!strcmp(fam,"U5"))  return 24*lq+log1p(-pow(q,-2))+log1p(pow(q,-3))+log1p(-pow(q,-4))+log1p(pow(q,-5))-log(5.0);
    return 0;
}
static void finish(const char*fam,const char*sz,long long n,u64 q,long long l,int f1,int N,const char*why){
    u64 p; int f=prime_power(q,&p);
    if(getenv("V38V")) printf("  gapwin %-6s n=%lld q=%llu f1=%d l=%lld ppow=%d\n",fam,n,q,f1,l,f);
    if(!f) return;
    double lS=logS_lie((double)q,sz);
    double lC4=log((double)n)+log((double)(n-1))+log((double)(n-2))+log((double)(n-3))-log(24.0);
    if(getenv("V38V")) printf("    -> p=%llu f=%d  lS=%.3f lC4=%.3f  l*f*N=%lld vp=%lld  l*lS=%.1f logn!=%.1f\n",p,f,lS,lC4,(long long)l*f*N,vp_fact(n,p),(double)l*lS,lgamma((double)n+1.0)-log(2.0));
    if(getenv("V42SIZE") && lS<=lC4) return;   /* v_task42: SIZE dropped (it used (*)) */
    if((i128)l*f*N > (i128)vp_fact(n,p)) return;
    if((double)l*lS > lgamma((double)n+1.0)-log(2.0)) return;
    nsurv++;
    printf("SURVIVOR %-6s n=%lld q=%llu (p=%llu,f=%d) f1=%d l*=%lld [%s]\n",fam,n,q,p,f,f1,l,why);
}
/* --------- exact shape solvers, i128 arithmetic --------- */
static u64 iroot(i128 v,int k){
    if(v<=0) return 0;
    double x=pow((double)(long double)v,1.0/k); u64 b=(u64)(x+0.5); return b<2?2:b;
}
static u64 sh_L3(i128 I){                 /* q^2+q+1 */
    if(I<3) return 0; i128 d=4*I-3; u64 s=(u64)(sqrt((double)(long double)d)+0.5);
    for(u64 c=(s>2?s-2:2);c<=s+2;c++) if((i128)c*c==d && c>=3 && (c-1)%2==0) return (c-1)/2;
    return 0;
}
static u64 sh_cyc(i128 I,int d){          /* 1+q+...+q^{d-1} */
    u64 b=iroot(I,d-1);
    for(u64 c=(b>2?b-2:2);c<=b+2;c++){ i128 v=0,t=1; int of=0;
        for(int i=0;i<d;i++){ v+=t; if(v>I){of=1;break;} if(t>(i128)1<<100){of=1;break;} t*=(i128)c; }
        if(!of && v==I) return c; }
    return 0;
}
static u64 sh_q3(i128 I){                 /* (q+1)(q^2+1) */
    u64 b=iroot(I,3);
    for(u64 c=(b>2?b-2:2);c<=b+2;c++){ i128 v=(i128)(c+1)*((i128)c*c+1); if(v==I) return c; }
    return 0;
}
static u64 sh_U4(i128 I){                 /* (q+1)(q^3+1) */
    u64 b=iroot(I,4);
    for(u64 c=(b>2?b-2:2);c<=b+2;c++){ i128 v=(i128)(c+1)*((i128)c*c*c+1); if(v==I) return c; }
    return 0;
}
static u64 sh_U5(i128 I){                 /* (q^5+1)(q^2+1) */
    u64 b=iroot(I,7);
    for(u64 c=(b>2?b-2:2);c<=b+2;c++){ i128 c5=(i128)c*c*c*c*c; i128 v=(c5+1)*((i128)c*c+1); if(v==I) return c; }
    return 0;
}
/* --------------- per (n, l) family test --------------- */
static void test_all(long long n,i128 C3,long long l){
    i128 D=C3/(i128)l;
    i128 g=n-3;              /* v_task42: comparisons below use 4*R > 3*g, i.e. R > 3(n-3)/4 */
    i128 lo=9*(i128)(n-3)*(n-3)/16;   /* v_task42: gap 3(n-3)/4 => q >= 3(n-3)/4 */
    if(D<lo) return;
    u64 q,p; int f;
    for(int f1=1;f1<=2;f1++){
        if(D%f1) continue;
        i128 I=D/f1; if(I<lo) continue;
        /* L3 */
        if((q=sh_L3(I))&&q>=3){ nshape++; shf[0]++;
            if(4*(i128)(q+1)>3*g*f1){ ngapwin++; finish("L3","L3",n,q,l,f1,3,"R=(q+1)/f1"); } }
        /* L4 / S4 share iota1 = (q+1)(q^2+1) */
        if((q=sh_q3(I))&&q>=2){ nshape++; shf[1]++;
            if(4*((i128)q*q+q+1) > 3*g*(i128)(q+1)*f1){ ngapwin++; finish("L4","L4",n,q,l,f1,6,"R=(q^2+q+1)/((q+1)f1)"); }
            f=prime_power(q,&p);
            if(f){
                if(p!=2&&f==1&&q>=5&&f1==1){ if(4*(i128)q*q > 3*g*2*(i128)(q+1)){ ngapwin++; finish("S4p","S4",n,q,l,1,4,"R=q^2/(2(q+1))"); } }
                else if(p!=2&&f>=2&&f1==1){ i128 t2=2*(i128)(q-1)/(i128)(p-1); if(4*t2>3*g){ ngapwin++; finish("S4np","S4",n,q,l,1,4,"R<=2t(q)"); } }
                else if(p==2&&f>=2){ i128 t2=(i128)q-1; if(4*t2>3*g){ ngapwin++; finish("S4e","S4",n,q,l,f1,4,"R=t(q)<=q-1"); } }
            } }
        /* L5 */
        if((q=sh_cyc(I,5))&&q>=2){ nshape++; shf[2]++;
            if(4*((i128)q*q+1)>3*g){ ngapwin++; finish("L5","L5",n,q,l,f1,10,"R=q^2+1"); } }
        if(f1>1) continue;
        /* U4 */
        if((q=sh_U4(I))&&q>=3){ nshape++; shf[3]++;
            if(4*((i128)q*q+1) > 3*g*(i128)(q+1)){ ngapwin++; finish("U4","U4",n,q,l,1,6,"R=(q^2+1)/(q+1)"); } }
        /* Sp6 */
        if((q=sh_cyc(I,6))&&q>=2){ nshape++; shf[4]++; f=prime_power(q,&p);
            if(f==1){ if(4*((i128)q*q*q*q-1) > 3*g*((i128)q*q*q-1)){ ngapwin++; finish("Sp6p","Sp6",n,q,l,1,9,"R=(q^4-1)/(q^3-1)"); } }
            else if(f>=2){ i128 t2=2*(i128)(q-1)/(i128)(p-1); if(4*t2>3*g){ ngapwin++; finish("Sp6np","Sp6",n,q,l,1,9,"R<=2t(q)"); } } }
        /* U5 */
        if((q=sh_U5(I))&&q>=2){ nshape++; shf[5]++; f=prime_power(q,&p);
            if(f==1){ if(4*((i128)q*q*q*q) > 3*g*(i128)(q+1)*((i128)q*q+1)){ ngapwin++; finish("U5p","U5",n,q,l,1,10,"R=q^4/((q+1)(q^2+1))"); } }
            else if(f>=2){ i128 t2=(i128)(q-1)/(i128)(p-1); if(4*t2>3*g){ ngapwin++; finish("U5np","U5",n,q,l,1,10,"R=t(q)"); } } }
    }
}
/* ---------------- divisors <= bound ---------------- */
static u64 pr[64]; static int ex[64], np_;
static u64 divbuf[8192]; static int ndiv;
static void gen(int i,u64 cur,u64 bound){
    if(i==np_){ if(ndiv<8192) divbuf[ndiv++]=cur; return; }
    u64 v=cur;
    for(int e=0;e<=ex[i];e++){ if(v>bound) break; gen(i+1,v,bound); if(v>bound/pr[i]) break; v*=pr[i]; }
}
static void addfac(long long m,int sgn,u64*P,int*E,int*np){
    while(m>1){ int p=spf[m],e=0; while(m%p==0){m/=p;e++;}
        int j; for(j=0;j<*np;j++) if(P[j]==(u64)p) break;
        if(j==*np){P[j]=p;E[j]=0;(*np)++;}
        E[j]+=sgn*e; }
}
int main(int argc,char**argv){
    NMAX=(argc>1)?atoll(argv[1]):20000000LL;
    printf("# v_task42 R1 scan, WEAKENED GAP R^p > 3(n-3)/4, SIZE filter dropped -- complete over ALL q, for 10 <= n <= %lld\n",NMAX);
    spf=malloc((NMAX+1)*sizeof(int));
    memset(spf,0,(NMAX+1)*sizeof(int));
    for(long long i=2;i<=NMAX;i++){ if(!spf[i]) for(long long j=i;j<=NMAX;j+=i) if(!spf[j]) spf[j]=(int)i; }
    for(long long n=10;n<=NMAX;n++){
        i128 C3=(i128)n*(n-1)*(n-2)/6;
        u64 P[64]; int E[64]; int nn=0;
        addfac(n,1,P,E,&nn); addfac(n-1,1,P,E,&nn); addfac(n-2,1,P,E,&nn); addfac(6,-1,P,E,&nn);
        np_=0; for(int i=0;i<nn;i++) if(E[i]>0){ pr[np_]=P[i]; ex[np_]=E[i]; np_++; }
        ndiv=0; gen(0,1,(u64)(16*(n/9)+8));   /* v_task42: l <= C(n,3)/lo ~ 0.30n; 16n/9+8 is generous */
        for(int i=0;i<ndiv;i++){ u64 l=divbuf[i]; test_all(n,C3,(long long)l); }
        if(n%2000000==0) fprintf(stderr,"  n=%lld\n",n);
    }
    printf("# per-shape hits L3=%lld q3(L4/S4)=%lld cyc5(L5)=%lld U4=%lld cyc6(Sp6)=%lld U5=%lld\n",shf[0],shf[1],shf[2],shf[3],shf[4],shf[5]);
    printf("# shape hits (iota1 realised by some q): %lld\n",nshape);
    printf("# gap windows entered: %lld\n",ngapwin);
    printf("# SURVIVORS: %lld\n",nsurv);
    return 0;
}
