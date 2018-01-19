#include<stdio.h>
#include<algorithm>
using namespace std;
const int N=400005,M=1500005,Inf=1e9;

int n,m,k,a[N],Val[N];
struct Info{
	int Min,Max,R_L,L_R;
	Info(){
		this->Min=Inf,this->Max=-Inf;
		this->R_L=this->L_R=-Inf;
	}
};
//Sigment Tree
namespace SMT{
	int Totn,Root,Son[M][2],Lazy[M];
	Info T[M];
	void PushUp(int p){
		int ls=Son[p][0],rs=Son[p][1];
		T[p].Max=max(T[ls].Max,T[rs].Max);
		T[p].Min=min(T[ls].Min,T[rs].Min);
		T[p].R_L=max(T[rs].Max-T[ls].Min,max(T[ls].R_L,T[rs].R_L));
		T[p].L_R=max(T[ls].Max-T[rs].Min,max(T[ls].L_R,T[rs].L_R));
	}
	void Setv(int p,int d){
		T[p].Max=T[p].Min=Lazy[p]=d;
		T[p].L_R=T[p].R_L=0;
	}
	void Putdown(int p){
		Setv(Son[p][0],Lazy[p]);
		Setv(Son[p][1],Lazy[p]);
		Lazy[p]=0;
	}
	void Build(int &p,int l,int r){
		p=++Totn;
		if(l<r){
			int mid=l+r>>1;
			Build(Son[p][0],l,mid);
			Build(Son[p][1],mid+1,r);
			PushUp(p);
		}else T[p].Max=T[p].Min=Val[l],T[p].L_R=T[p].R_L=0;
	}
	void Modify(int p,int l,int r,int x,int y,int d){
		if(Lazy[p])Putdown(p);
		if(x<=l&&r<=y){
			Setv(p,d);
			return;
		}
		int mid=l+r>>1;
		if(l<=y&&mid>=x)Modify(Son[p][0],l,mid,x,y,d);
		if(mid<y&&r>=x)Modify(Son[p][1],mid+1,r,x,y,d);
		PushUp(p);
	}
	Info Query(int p,int l,int r,int x,int y){
		if(Lazy[p])Putdown(p);
		if(x<=l&&r<=y)return T[p];
		int mid=l+r>>1;
		Info lm,rm,ret;
		if(l<=y&&mid>=x)lm=Query(Son[p][0],l,mid,x,y);
		if(mid<y&&r>=x)rm=Query(Son[p][1],mid+1,r,x,y);
		ret.L_R=max(max(lm.L_R,rm.L_R),lm.Max-rm.Min);
		ret.R_L=max(max(lm.R_L,rm.R_L),rm.Max-lm.Min);
		ret.Max=max(lm.Max,rm.Max);
		ret.Min=min(lm.Min,rm.Min);
		return ret;
	}
}
int Tote,End[N],Last[N],Next[N];
void Ins(int x,int y){
	End[++Tote]=y;
	Next[Tote]=Last[x];
	Last[x]=Tote;
}
int vt,Root,Fa[N],Dep[N],Top[N],Son[N],In[N],Out[N];
int FindHeavy(int x,int fa){
	Fa[x]=fa;
	Dep[x]=Dep[fa]+1;
	int u,Size=1,tmp,Maxx=0;
	for(int i=Last[x];i;i=Next[i]){
		u=End[i];
		if(u!=fa){
			tmp=FindHeavy(u,x);
			Size+=tmp;
			if(tmp>Maxx)Maxx=tmp,Son[x]=u;
		}
	}
	return Size;
}
void LinkHeavy(int x,int anc){
	In[x]=++vt,Top[x]=anc;
	if(Son[x])LinkHeavy(Son[x],anc);
	int u;
	for(int i=Last[x];i;i=Next[i]){
		u=End[i];
		if(!In[u])LinkHeavy(u,u);
	}
	Out[x]=vt;
}
void ModLine(int x,int y,int d){
	while(Top[x]!=Top[y]){
		if(Dep[Top[x]]>Dep[Top[y]])swap(x,y);
		SMT::Modify(1,1,n,In[Top[y]],In[y],d);
		y=Fa[Top[y]];
	}
	if(Dep[x]>Dep[y])swap(x,y);
	SMT::Modify(1,1,n,In[x],In[y],d);
}
int GetBr(int x,int y){
	while(Top[x]!=Top[y]){
		if(Fa[Top[y]]==x)return Top[y];
		y=Fa[Top[y]];
	}
	return Son[x];
}
void ModSub(int x,int d){
	if(x!=Root&&In[Root]>In[x]&&In[Root]<=Out[x]){
		int y=GetBr(x,Root);
		SMT::Modify(1,1,n,1,In[y]-1,d);
		SMT::Modify(1,1,n,Out[y]+1,n,d);
	}
	else SMT::Modify(1,1,n,In[x],Out[x],d);
}
int Getans(int x,int y){
	int LMin=Inf,RMax=-Inf,Ans=-Inf;
	Info tmp;
	while(Top[x]!=Top[y]){
		if(Dep[Top[x]]>Dep[Top[y]]){
			tmp=SMT::Query(1,1,n,In[Top[x]],In[x]);
			Ans=max(Ans,max(tmp.L_R,tmp.Max-LMin));
			LMin=min(LMin,tmp.Min);
			x=Fa[Top[x]];
		}
		else{
			tmp=SMT::Query(1,1,n,In[Top[y]],In[y]);
			Ans=max(Ans,max(tmp.R_L,RMax-tmp.Min));
			RMax=max(RMax,tmp.Max);
			y=Fa[Top[y]];
		}
	}
	if(Dep[x]<Dep[y]){
		tmp=SMT::Query(1,1,n,In[x],In[y]);
		Ans=max(Ans,max(tmp.R_L,max(RMax-tmp.Min,tmp.Max-LMin)));
	}
	else{
		tmp=SMT::Query(1,1,n,In[y],In[x]);
		Ans=max(Ans,max(tmp.L_R,max(RMax-tmp.Min,tmp.Max-LMin)));
	}
	return max(Ans,RMax-LMin);
}
int main(){
	// freopen("starkmal.in","r",stdin);
	int opt,x,y,z;
	scanf("%d%d",&n,&k);
	for(int i=1;i<=n;i++)scanf("%d",&a[i]);
	for(int i=1;i<n;i++){
		scanf("%d%d",&x,&y);
		Ins(x,y);
		Ins(y,x);
	}
	Root=k;
	FindHeavy(Root,0);
	LinkHeavy(Root,Root);
	for(int i=1;i<=n;i++)Val[In[i]]=a[i];
	SMT::Build(SMT::Root,1,n);

	scanf("%d",&m);
	for(int i=1;i<=m;i++){
		scanf("%d",&opt);
		if(opt==0){
			scanf("%d%d%d",&x,&y,&z);
			ModLine(x,y,z);
		}
		else if(opt==1){
			scanf("%d%d",&x,&z);
			ModSub(x,z);
		}
		else if(opt==2)scanf("%d",&Root);
		else {
			scanf("%d%d",&x,&y);
			printf("%d\n",Getans(x,y));
		}
	}
}
