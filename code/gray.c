// Exact min-unsat of a 3-XOR system by Gray-code enumeration over free variables.
// usage: gray instance.txt [fixed_vars_file]   (fixed vars are held at 0: gauge pivots)
#include <stdio.h>
#include <stdlib.h>
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"r"); int n,m; if(fscanf(f,"%d %d",&n,&m)!=2) return 1;
  int*L=malloc(12*m),*s=malloc(4*m),*deg=calloc(n,4);
  for(int i=0;i<m;i++){ if(fscanf(f,"%d %d %d %d",&L[3*i],&L[3*i+1],&L[3*i+2],&s[i])!=4) return 1; for(int k=0;k<3;k++) deg[L[3*i+k]]++; }
  int**inc=malloc(sizeof(int*)*n),*fl=calloc(n,4); for(int v=0;v<n;v++) inc[v]=malloc(4*deg[v]+4);
  for(int i=0;i<m;i++) for(int k=0;k<3;k++){int v=L[3*i+k]; inc[v][fl[v]++]=i;}
  int*fixed=calloc(n,4); if(argc>2){FILE*g=fopen(argv[2],"r"); int v; while(fscanf(g,"%d",&v)==1) fixed[v]=1;}
  int fr[64],nf=0; for(int v=0;v<n;v++) if(!fixed[v]) fr[nf++]=v;
  if(nf>44){fprintf(stderr,"too many free vars %d\n",nf); return 2;}
  int*viol=malloc(4*m); int cur=0; for(int i=0;i<m;i++){viol[i]=s[i]; cur+=viol[i];}
  int best=cur; unsigned long long N=1ULL<<nf;
  for(unsigned long long g=1; g<N; g++){
    int b=__builtin_ctzll(g); int v=fr[b];
    for(int k=0;k<deg[v];k++){int i=inc[v][k]; cur+= viol[i]? -1:1; viol[i]^=1;}
    if(cur<best) best=cur;
  }
  printf("%d %d %d\n",best,nf,m); return 0;
}
