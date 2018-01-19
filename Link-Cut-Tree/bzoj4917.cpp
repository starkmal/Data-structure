#include<stdio.h>
#include<ctype.h>
#include<algorithm>
#include<vector>
using namespace std;
const int N=100005;

inline int _R(){
	int d=0;char t=getchar();
	while(!isdigit(t))t=getchar();
	for(;isdigit(t);t=getchar())d=(d<<3)+(d<<1)+t-'0';
	return d;
}

int n,m;
int Tote,Last[N],Next[N<<1],End[N<<1];
void Ins(int x,int y){
	End[++Tote]=y;
	Next[Tote]=Last[x];
	Last[x]=Tote;
}

int vtt,g[N],In[N],Out[N],Anc[N][22],Dep[N];
void Dfs(int x,int fa){
	Dep[x]=Dep[fa]+1;
	for(int i=1;i<=20;i++)Anc[x][i]=Anc[Anc[x][i-1]][i-1];
	In[x]=++vtt;
	g[In[x]]=Dep[fa];
	for(int i=Last[x],u;i;i=Next[i])
		if((u=End[i])!=fa){
			Anc[u][0]=x;
			Dfs(u,x);
		}
	Out[x]=vtt;
}
int LCA(int x,int y){
	if(Dep[x]>Dep[y])swap(x,y);
	int i,t=Dep[y]-Dep[x];
	for(i=0;i<=20;i++)
		if((1<<i)&t)y=Anc[y][i];
	if(x==y)return x;
	for(i=20;i>=0;i--)
		if(Anc[x][i]!=Anc[y][i])
			x=Anc[x][i],y=Anc[y][i];
	return Anc[x][0];
}

namespace SegTree{
//private
	struct Node{
		Node* Son[2];
		int Val,Lazy,Tot,Max;		//Val值记录到根**虚边**的数量
	}*Root,*null,*tl,pool[N<<3];

	void PushUp(Node* p){	//不能在叶子节点调用哦
		p->Max=max(p->Son[0]->Max,p->Son[1]->Max);
	}
	void Build(Node* &p,int l,int r){
		p=++tl;
		p->Tot=r-l+1;
		if(l<r){
			int mid=l+r>>1;
			Build(p->Son[0],l,mid);
			Build(p->Son[1],mid+1,r);
			PushUp(p);
		}
		else{
			p->Son[0]=p->Son[1]=null;
			p->Val=p->Max=g[l];
		}
	}
	void Setv(Node* p,int d){
		p->Val+=p->Tot*d;
		p->Lazy+=d;
		p->Max+=d;
	}
	void Putdown(Node* p){
		if(p->Son[0]!=null)Setv(p->Son[0],p->Lazy);
		if(p->Son[1]!=null)Setv(p->Son[1],p->Lazy);
		p->Lazy=0;
	}
	void Modify(Node* p,int l,int r,int x,int y,int d){
		if(p->Lazy)Putdown(p);
		if(x<=l&&r<=y){
			Setv(p,d);
			return;
		}
		int mid=l+r>>1;
		if(l<=y&&mid>=x)Modify(p->Son[0],l,mid,x,y,d);
		if(mid<y&&r>=x)Modify(p->Son[1],mid+1,r,x,y,d);
		PushUp(p);
	}
	int GetMax(Node* p,int l,int r,int x,int y){
		if(p->Lazy)Putdown(p);
		if(x<=l&&r<=y)return p->Max;
		int mid=l+r>>1,lm=0,rm=0;
		if(l<=y&&mid>=x)lm=GetMax(p->Son[0],l,mid,x,y);
		if(mid<y&&r>=x)rm=GetMax(p->Son[1],mid+1,r,x,y);
		return max(lm,rm);
	}
	int GetVal(Node* p,int l,int r,int k){
		if(p->Lazy)Putdown(p);
		if(l==r)return p->Val;
		int mid=l+r>>1;
		if(k<=mid)return GetVal(p->Son[0],l,mid,k);
		else return GetVal(p->Son[1],mid+1,r,k);
	}
//public
	void ModSub(int x,int d){
		Modify(Root,1,n,In[x],Out[x],d);
	}
	int GetAns(int x){
		return GetMax(Root,1,n,In[x],Out[x])+1;
	}
	int GetLine(int x,int y){
		return GetVal(Root,1,n,In[x])+
			   GetVal(Root,1,n,In[y])-
			   GetVal(Root,1,n,In[LCA(x,y)])*2+1;
	}
	void Init(){
		Root=null=tl=pool;
		null->Son[0]=null->Son[1]=null;
		null->Val=null->Lazy=0;
		Build(Root,1,n);
	}
}

namespace LCT{
//private
	struct Node{
		Node *Son[2],*Fa;
		int id;
	}*id[N],*null,pool[N];

	void Dfs(int x,int fa){
		id[x]->Fa=id[fa];
		for(int i=Last[x];i;i=Next[i])
			if(End[i]!=fa)Dfs(End[i],x);
	}
	inline bool isRoot(Node* p){
		return p->Fa==null||(p->Fa->Son[0]!=p&&p->Fa->Son[1]!=p);
	}
	inline void Rotate(Node* x){
		Node *y=x->Fa,*z=y->Fa;
		int l=y->Son[0]==x,r=l^1;
		if(!isRoot(y))z->Son[z->Son[1]==y]=x;x->Fa=z;
		y->Son[r]=x->Son[l],x->Son[l]->Fa=y,x->Son[l]=y,y->Fa=x;
	}
	void Splay(Node* x){
		while(!isRoot(x)){
			Node *y=x->Fa,*z=y->Fa;
			if(!isRoot(y)){
				if(y->Son[0]==x^z->Son[0]==y)Rotate(x);
				else Rotate(y);
			}
			else Rotate(x);
		}
	}
//public
	void Init(){
		null=pool;
		null->Son[0]=null->Son[1]=null->Fa=null;
		for(int i=1;i<=n;i++){
			id[i]=pool+i;
			id[i]->id=i;
			id[i]->Son[0]=id[i]->Son[1]=id[i]->Fa=null;
		}
		id[0]=null;
		Dfs(1,0);
	}
	void Access(int _x){
		Node *x=id[_x],*tmp;
		for(Node* t=null;x!=null;t=x,x=x->Fa){
			Splay(x);
			if(x->Son[1]!=null){
				tmp=x->Son[1];
				while(tmp->Son[0]!=null)tmp=tmp->Son[0];
				SegTree::ModSub(tmp->id,1);			//实边变虚边
			}
			x->Son[1]=t;
			if(t!=null){
				tmp=t;
				while(tmp->Son[0]!=null)tmp=tmp->Son[0];
				SegTree::ModSub(tmp->id,-1);		//虚边变实边
			}
		}
	}
}

int main(){
	int i,j,k,x,y,opt;
	n=_R(),m=_R();
	for(i=1;i<n;i++){
		x=_R(),y=_R();
		Ins(x,y),Ins(y,x);
	}
	Dfs(1,0);
	SegTree::Init();
	LCT::Init();
	for(i=1;i<=m;i++){
		opt=_R();
		if(opt==1){
			x=_R();
			LCT::Access(x);
		}
		else if(opt==2){
			x=_R(),y=_R();
			printf("%d\n",SegTree::GetLine(x,y));
		}
		else {
			x=_R();
			printf("%d\n",SegTree::GetAns(x));
		}
	}
}
