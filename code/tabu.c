// Tabu search for MIN-UNSAT of 3-XOR systems (contextuality degree upper bounds).
// usage: tabu instance.txt seconds seed [out_assignment]
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>

int n, m; int *L; int *sg; int *deg; int **inc; int *x; int *viol; int *dlt; long *tabu;

static double now(){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+1e-9*t.tv_nsec; }
static unsigned long long rs;
static unsigned rnd(){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return (unsigned)(rs>>11); }

int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"r"); double T=atof(argv[2]); rs=88172645463325252ULL^((unsigned long long)atoi(argv[3])*2654435761ULL);
  if(fscanf(f,"%d %d",&n,&m)!=2) return 1;
  L=malloc(sizeof(int)*3*m); sg=malloc(sizeof(int)*m); deg=calloc(n,sizeof(int));
  for(int i=0;i<m;i++){ if(fscanf(f,"%d %d %d %d",&L[3*i],&L[3*i+1],&L[3*i+2],&sg[i])!=4) return 1; for(int k=0;k<3;k++) deg[L[3*i+k]]++; }
  inc=malloc(sizeof(int*)*n); int*fill=calloc(n,sizeof(int)); for(int v=0;v<n;v++) inc[v]=malloc(sizeof(int)*deg[v]);
  for(int i=0;i<m;i++) for(int k=0;k<3;k++){int v=L[3*i+k]; inc[v][fill[v]++]=i;}
  x=calloc(n,sizeof(int)); viol=calloc(m,sizeof(int)); dlt=calloc(n,sizeof(int)); tabu=calloc(n,sizeof(long));
  int *bestx=malloc(sizeof(int)*n); int best=m+1; double t0=now(); long it=0;
  while(now()-t0<T){
    for(int v=0;v<n;v++){x[v]=rnd()&1; tabu[v]=0;}
    int cur=0; for(int i=0;i<m;i++){viol[i]=(x[L[3*i]]^x[L[3*i+1]]^x[L[3*i+2]]^sg[i]); cur+=viol[i];}
    for(int v=0;v<n;v++){int d=0; for(int k=0;k<deg[v];k++) d+= viol[inc[v][k]]?-1:1; dlt[v]=d;}
    int rbest=cur; long last_imp=0; long step=0;
    while(step-last_imp<200000 && now()-t0<T){
      step++; it++;
      int bv=-1,bd=1<<30,cnt=0;
      for(int v=0;v<n;v++){
        int d=dlt[v]; int ok = tabu[v]<=step || cur+d<best;
        if(!ok) continue;
        if(d<bd){bd=d;bv=v;cnt=1;} else if(d==bd){cnt++; if(rnd()%cnt==0) bv=v;}
      }
      if(bv<0) continue;
      x[bv]^=1; cur+=bd;
      for(int k=0;k<deg[bv];k++){int i=inc[bv][k]; viol[i]^=1; int ch = viol[i]? -2: 2; // line became violated: neighbours' delta decreases
        for(int t=0;t<3;t++){int u=L[3*i+t]; if(u!=bv) dlt[u]+=ch;}}
      dlt[bv]=-dlt[bv];
      tabu[bv]=step+5+rnd()%(n/8+1);
      if(cur<rbest){rbest=cur; last_imp=step;}
      if(cur<best){best=cur; memcpy(bestx,x,sizeof(int)*n); fprintf(stderr,"  best %d at %.1fs\n",best,now()-t0);}
    }
  }
  printf("%d %ld\n",best,it);
  if(argc>4){FILE*g=fopen(argv[4],"w"); for(int v=0;v<n;v++) fprintf(g,"%d\n",bestx[v]); fclose(g);}
  return 0;
}
