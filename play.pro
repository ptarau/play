% a Prolog playground for lambda terms, combinators, types
% and tree-based arithmetic
:-use_module(library(lists)).

dbTermSize(v(_),0).
dbTermSize(l(A),R):-
  dbTermSize(A,RA),
  R is RA+1.
dbTermSize(a(A,B),R):-
  dbTermSize(A,RA),
  dbTermSize(B,RB),
  R is 1+RA+RB.

isClosedB(T):-isClosed1B(T,0).

isClosed1B(v(N),D):-N<D.
isClosed1B(l(A),D):-D1 is D+1,
  isClosed1B(A,D1).
isClosed1B(a(X,Y),D):-
  isClosed1B(X,D),
  isClosed1B(Y,D).

b2l(A,T):-b2l(A,T,_Vs).

b2l(v(I),V,Vs):-nth0(I,Vs,V).
b2l(a(A,B),a(X,Y),Vs):-b2l(A,X,Vs),b2l(B,Y,Vs).
b2l(l(A),l(V,Y),Vs):-b2l(A,Y,[V|Vs]).

l2b(A,T):-copy_term(A,CA),numbervars(CA,0,_),l2b(CA,T,_Vs).

l2b('$VAR'(V),v(I),Vs):-once(nth0(I,Vs,'$VAR'(V))).
l2b(a(X,Y),a(A,B),Vs):-l2b(X,A,Vs),l2b(Y,B,Vs).
l2b(l(V,Y),l(A),Vs):-l2b(Y,A,[V|Vs]).

b2c(v(X),v(0,X)). 
b2c(a(X,Y),a(0,A,B)):-b2c(X,A),b2c(Y,B). 
b2c(l(X),R):-b2c1(0,X,R).

b2c1(K,a(X,Y),a(K1,A,B)):-up(K,K1),b2c(X,A),b2c(Y,B).
b2c1(K, v(X),v(K1,X)):-up(K,K1).
b2c1(K,l(X),R):-up(K,K1),b2c1(K1,X,R).  

up(From,To):-From>=0,To is From+1.

c2b(v(K,X),R):-X>=0,iterLam(K,v(X),R).
c2b(a(K,X,Y),R):-c2b(X,A),c2b(Y,B),iterLam(K,a(A,B),R).

iterLam(0,X,X).
iterLam(K,X,l(R)):-down(K,K1),iterLam(K1,X,R).

down(From,To):-From>0,To is From-1. 

c2l --> c2b,b2l.
l2c --> l2b,b2c.

isClosedC(T):-isClosedC(T,0).
  
isClosedC(v(K,N),S):-N<S+K.
isClosedC(a(K,X,Y),S1):-S2 is S1+K,isClosedC(X,S2),isClosedC(Y,S2).

extractType(X,TX):-var(X),!,TX=X. % this matches all variables
extractType(l(TX,A),(TX>TA)):-extractType(A,TA).
extractType(a(A,B),TY):-extractType(A,(TX>TY)),extractType(B,TX).

polyTypeOf(LTerm,Type):-
  extractType(LTerm,Type),
  acyclic_term(LTerm).

bindTypeB(x):-!.
bindTypeB((A>B)):-bindTypeB(A),bindTypeB(B).  

hasType(CTerm,Type):-
  c2l(CTerm,LTerm),
  polyTypeOf(LTerm,Type),
  bindTypeB(Type).

typable(Term):-hasType(Term,_Type).

deBruijnTypeOf(v(I),V,Vs):-
  nth0(I,Vs,V0),
  unify_with_occurs_check(V,V0).
deBruijnTypeOf(a(A,B),Y,Vs):-
  deBruijnTypeOf(A,(X>Y),Vs),
  deBruijnTypeOf(B,X,Vs).
deBruijnTypeOf(l(A),(X>Y),Vs):-
  deBruijnTypeOf(A,Y,[X|Vs]).

boundTypeOf(A,T):-deBruijnTypeOf(A,T0,[]),bindTypeB(T0),!,T=T0.

genTreeByDepth(_,x).
genTreeByDepth(D1,(X>Y)):-down(D1,D2),
  genTreeByDepth(D2,X),
  genTreeByDepth(D2,Y).

genTree(N,T):-genTree(T,N,0).
 
genTree(x)-->[].
genTree((X>Y))-->down,
  genTree(X),
  genTree(Y).

tsize(x,0).
tsize((X>Y),S):-tsize(X,A),tsize(Y,B),S is 1+A+B.

motzkinTree(L,T):-motzkinTree(T,L,0).

motzkinTree(u)-->down.
motzkinTree(l(A))-->down,motzkinTree(A).
motzkinTree(a(A,B))-->down,motzkinTree(A),motzkinTree(B).

genLambda(L,T):-genLambda(T,[],L,0).

genLambda(X,Vs)-->{member(X,Vs)}.
genLambda(l(X,A),Vs)-->down,genLambda(A,[X|Vs]).
genLambda(a(A,B),Vs)-->down,genLambda(A,Vs),genLambda(B,Vs).

genDBterm(v(X),V)-->
  {down(V,V0)},
  {between(0,V0,X)}.
genDBterm(l(A),V)-->down,
  {up(V,NewV)},
  genDBterm(A,NewV).
genDBterm(a(A,B),V)-->down,
  genDBterm(A,V),
  genDBterm(B,V).  



genDBterm(L,T):-genDBterm(T,0,L,0).

genDBterms(L,T):-genDBterm(T,0,L,_).

genCompressed --> genDBterm,b2c.
genCompresseds--> genDBterms,b2c.

genStandard-->genDBterm,b2l.
genStandards-->genDBterms,b2l.

nf(v(X),V)-->{down(V,V0),between(0,V0,X)}.
nf(l(A),V)-->down,{up(V,NewV)},nf(A,NewV).
nf(a(v(X),B),V)-->down,nf(v(X),V),nf(B,V).  
nf(a(a(X,Y),B),V)-->down,nf(a(X,Y),V),nf(B,V).  

nf(L,T):-nf(B,0,L,0),b2c(B,T).
nfs(L,T):-nf(B,0,L,_),b2c(B,T).

linLamb(X,[X])-->[].
linLamb(l(X,A),Vs)-->down,linLamb(A,[X|Vs]).
linLamb(a(A,B),Vs)-->down,
  {subset_and_complement_of(Vs,As,Bs)},
  linLamb(A,As),linLamb(B,Bs).

subset_and_complement_of([],[],[]).
subset_and_complement_of([X|Xs],NewYs,NewZs):-
  subset_and_complement_of(Xs,Ys,Zs),
  place_element(X,Ys,Zs,NewYs,NewZs).

place_element(X,Ys,Zs,[X|Ys],Zs).
place_element(X,Ys,Zs,Ys,[X|Zs]).

linLamb(L,CT):-linLamb(T,[],L,0),l2c(T,CT).

afLinLamb(L,CT):-afLinLamb(T,[],L,0),l2c(T,CT).

afLinLamb(X,[X|_])-->[].
afLinLamb(l(X,A),Vs)-->down,afLinLamb(A,[X|Vs]).
afLinLamb(a(A,B),Vs)-->down,
  {subset_and_complement_of(Vs,As,Bs)},
  afLinLamb(A,As),afLinLamb(B,Bs).

boundedUnary(v(X),V,_D)-->{down(V,V0),between(0,V0,X)}.
boundedUnary(l(A),V,D1)-->down,
  {down(D1,D2),up(V,NewV)},
  boundedUnary(A,NewV,D2).
boundedUnary(a(A,B),V,D)-->down,
  boundedUnary(A,V,D),boundedUnary(B,V,D).  

boundedUnary(D,L,T):-boundedUnary(B,0,D,L,0),b2c(B,T).
boundedUnarys(D,L,T):-boundedUnary(B,0,D,L,_),b2c(B,T).

blc(L,T):-blc(L,T,_Cs).

blc(L,T,Cs):-length(Cs,L),blc(B,0,Cs,[]),b2c(B,T).

blc(v(X),V)-->{between(1,V,X)},encvar(X).
blc(l(A),V)-->[0,0],{NewV is V+1},blc(A,NewV).
blc(a(A,B),V)-->[0,1],blc(A,V),blc(B,V).  

encvar(0)-->[0].
encvar(N)-->{down(N,N1)},[1],encvar(N1).

genTypable(L,T):-genCompressed(L,T),typable(T).
genTypables(L,T):-genCompresseds(L,T),typable(T).

genTypedTerm1(L,Term,Type):-
  genDBterm(L,Term),
  boundTypeOf(Term,Type).

genTypedTerms1(L,Term,Type):-
  genDBterms(L,Term),
  boundTypeOf(Term,Type).

genTypedTerm(v(I),V,Vs)-->
  {
   nth0(I,Vs,V0),
   unify_with_occurs_check(V,V0)
  }.
genTypedTerm(a(A,B),Y,Vs)-->down,
  genTypedTerm(A,(X>Y),Vs),
  genTypedTerm(B,X,Vs).
genTypedTerm(l(A),(X>Y),Vs)-->down,
  genTypedTerm(A,Y,[X|Vs]).  

genTypedTerm(L,B,T):-
  genTypedTerm(B,T,[],L,0),
  bindTypeB(T).

genTypedTerms(L,B,T):-
  genTypedTerm(B,T,[],L,_),
  bindTypeB(T).

beta(l(A),B,R):-subst(A,0,B,R).

subst(a(A1,A2),I,B,a(R1,R2)):-I>=0,
  subst(A1,I,B,R1),
  subst(A2,I,B,R2).   
subst(l(A),I,B,l(R)):-I>=0,I1 is I+1,subst(A,I1,B,R).
subst(v(N),I,_B,v(N1)):-I>=0,N>I,N1 is N-1. 
subst(v(N),I,_B,v(N)):-I>=0,N<I.
subst(v(N),I,B,R):-I>=0,N=:=I,shift_var(I,0,B,R).

shift_var(I,K,a(A,B),a(RA,RB)):-K>=0,I>=0,
  shift_var(I,K,A,RA),
  shift_var(I,K,B,RB).
shift_var(I,K,l(A),l(R)):-K>=0,I>=0,K1 is K+1,shift_var(I,K1,A,R).
shift_var(I,K,v(N),v(M)):-K>=0,I>=0,N>=K,M is N+I.
shift_var(I,K,v(N),v(N)):-K>=0,I>=0,N<K.

wh_nf(v(X),v(X)).
wh_nf(l(E),l(E)).
wh_nf(a(X,Y),Z):-wh_nf(X,X1),wh_nf1(X1,Y,Z).

wh_nf1(v(X),Y,a(v(X),Y)).
wh_nf1(l(E),Y,Z):-beta(l(E),Y,NewE),wh_nf(NewE,Z).
wh_nf1(a(X1,X2),Y,a(a(X1,X2),Y)).

to_nf(v(X),v(X)).
to_nf(l(E),l(NE)):-to_nf(E,NE).
to_nf(a(E1,E2),R):-wh_nf(E1,NE),to_nf1(NE,E2,R).

to_nf1(v(E1),E2,a(v(E1),NE2)):-to_nf(E2,NE2).
to_nf1(l(E),E2,R):-beta(l(E),E2,NewE),to_nf(NewE,R).
to_nf1(a(A,B),E2,a(NE1,NE2)):-to_nf(a(A,B),NE1),to_nf(E2,NE2).

evalDeBruijn --> to_nf.

evalStandard-->l2b,to_nf,b2l.
evalCompressed-->c2b,to_nf,b2c.

genSK(k)-->[].
genSK(s)-->[].
genSK(X*Y)-->down,genSK(X),genSK(Y).

genSK(N,X):-genSK(X,N,0).

genSKs(N,X):-genSK(X,N,_).

csize(k,0).
csize(s,0).
csize((X*Y),S):-csize(X,A),csize(Y,B),S is 1+A+B.

evalSK(k,k).
evalSK(s,s). 
evalSK(F*G,R):-evalSK(F,F1),evalSK(G,G1),appSK(F1,G1,R).


appSK((s*X)*Y,Z,R):-!,  % S
  appSK(X,Z,R1),
  appSK(Y,Z,R2),
  appSK(R1,R2,R).
appSK(k*X,_Y,R):-!,R=X. % K  
appSK(F,G,F*G).

kB(l(l(v(1)))).

sB(l(l(l(a(a(v(2),v(0)),a(v(1),v(0))))))).

sk2b(s,S):-sB(S).
sk2b(k,K):-kB(K).
sk2b((X*Y),a(A,B)):-sk2b(X,A),sk2b(Y,B).

skTypeOf(k,(A>(_B>A))).  
skTypeOf(s,(((A>(B>C))> ((A>B)>(A>C) )))).
skTypeOf(A*B,Y):-
  skTypeOf(A,T),
  skTypeOf(B,X),
  unify_with_occurs_check(T,(X>Y)).

simpleTypeOf(A,T):-
  skTypeOf(A,T),
  bindWithBaseType(T).

% bind all variables with type 'x'
bindWithBaseType(x):-!. 
bindWithBaseType((A>B)):-
  bindWithBaseType(A),
  bindWithBaseType(B).

typableSK(X):-skTypeOf(X,_).

sT(x>(x>x)).
kT((x>x)>x).
xxT(x>x).

evalX((F>G),R):-!,evalX(F,F1),evalX(G,G1),appX(F1,G1,R).
evalX(X,X).

appX((((x>x)>x)>X),_Y,R):-!,R=X. % K
appX((((x>(x>x))>X)>Y),Z,R):-!,  % S
  appX(X,Z,R1),
  appX(Y,Z,R2),
  appX(R1,R2,R).
%app((((x>x)>_X)>Y),_Z,R):-!,R=Y. 
%app((x>x)>x,(x>x)>x,R):-!,app(x,x,R).
appX(F,G,(F>G)).

xB(X):-F=v(0),kB(K),sB(S),X=l(a(a(a(F,K),S),K)).

t2b(x,X):-xB(X).
t2b((X>Y),a(A,B)):-t2b(X,A),t2b(Y,B).

evalAsT --> evalX,t2b.
evalAsB --> t2b,evalDeBruijn.

xtype(X,T):-t2b(X,B),boundTypeOf(B,T).

xt(X,T):-poly_xt(X,T),bindTypeB(T).

xT(T):-t2b(x,B),boundTypeOf(B,T,[]).

poly_xt(x,T):-xT(T).
poly_xt(A>B,Y):-poly_xt(A,T),poly_xt(B,X),
  unify_with_occurs_check(T,(X>Y)).

catpar(T,Ps):-catpar(T,0,1,Ps,[]).
catpar(X,L,R) --> [L],catpars(X,L,R).

catpars(x,_,R) --> [R].
catpars((X>Xs),L,R)-->catpar(X,L,R),catpars(Xs,L,R). 

rankCatalan(Xs,R):-
  length(Xs,XL),XL>=2, 
  L is XL-2, I is L // 2,
  localRank(I,Xs,N),
  S is 0, PI is I-1,
  rankLoop(PI,S,NewS),
  R is NewS+N.

unrankCatalan(R,Xs):- 
  S is 0, I is 0,
  unrankLoop(R,S,I,NewS,NewI),
  LR is R-NewS, 
  L is 2*NewI+1,
  length(As,L),
  localUnrank(NewI,LR,As),
  As=[_|Bs], 
  append([0|Bs],[1],Xs).

rankType(T,Code):-
  catpar(T,Ps),
  rankCatalan(Ps,Code).
  
unrankType(Code,Term):-
  unrankCatalan(Code,Ps),
  catpar(Term,Ps).

cskel(S,Vs, T):-cskel(T,S,Vs,[]).

cskel(v(K,N),x)-->[K,N].
cskel(a(K,X,Y),(A>B))-->[K],cskel(X,A),cskel(Y,B).

toSkel(T,Skel,Vs):-
  cskel(T,Cat,Vs,[]),
  catpar(Cat,Skel).
  
fromSkel(Skel,Vs, T):-
  catpar(Cat,Skel),
  cskel(T,Cat,Vs,[]).

fromCantorTuple(Ns,N):-
  list2set(Ns,Xs),
  fromKSet(Xs,N).

fromKSet(Xs,N):-untuplingLoop(Xs,0,0,N).

untuplingLoop([],_L,B,B).
untuplingLoop([X|Xs],L1,B1,Bn):-L2 is L1+1, 
  binomial(X,L2,B),B2 is B1+B,
  untuplingLoop(Xs,L2,B2,Bn).  

toKSet(K,N,Ds):-combinatoriallDigits(K,N,[],Ds).

combinatoriallDigits(0,_,Ds,Ds).
combinatoriallDigits(K,N,Ds,NewDs):-K>0,K1 is K-1,
  upperBinomial(K,N,M),M1 is M-1,
  binomial(M1,K,BDigit),N1 is N-BDigit,
  combinatoriallDigits(K1,N1,[M1|Ds],NewDs).

upperBinomial(K,N,R):-S is N+K,
  roughLimit(K,S,K,M),L is M // 2,
  binarySearch(K,N,L,M,R).

roughLimit(K,N,I, L):-binomial(I,K,B),B>N,!,L=I.
roughLimit(K,N,I, L):-J is 2*I,
  roughLimit(K,N,J,L).

binarySearch(_K,_N,From,From,R):-!,R=From.
binarySearch(K,N,From,To,R):-Mid is (From+To) // 2,binomial(Mid,K,B),
  splitSearchOn(B,K,N,From,Mid,To,R).

splitSearchOn(B,K,N,From,Mid,_To,R):-B>N,!,
  binarySearch(K,N,From,Mid,R).
splitSearchOn(_B,K,N,_From,Mid,To,R):-Mid1 is Mid+1,
  binarySearch(K,N,Mid1,To,R).  

toCantorTuple(K,N,Ns):-
  toKSet(K,N,Ds),
  set2list(Ds,Ns).

rankTerm(Term,Code):-
  toSkel(Term,Ps,Ns),
  rankCatalan(Ps,CatCode),
  fromCantorTuple(Ns,VarsCode),
  fromCantorTuple([CatCode,VarsCode],Code).

unrankTerm(Code,Term):-
  toCantorTuple(2,Code,[CatCode,VarsCode]),
  unrankCatalan(CatCode,Ps), 
  length(Ps,L2),L is (L2-2) div 2, L3 is 3*L+2,
  toCantorTuple(L3,VarsCode,Ns),
  fromSkel(Ps,Ns,Term).

ogen(M,T):-between(0,M,I),unrankTerm(I,T).  

cgen(M,IT):-ogen(M,IT),isClosedC(IT).

tgen(M,IT):-cgen(M,IT),typable(IT).

cons(I,J,C) :- I>=0,J>=0,
  D is mod(J+1,2),
  C is 2^(I+1)*(J+D)-D.

decons(K,I1,J1):-K>0,B is mod(K,2),KB is K+B,
  dyadicVal(KB,I,J),
  I1 is max(0,I-1),J1 is J-B.

dyadicVal(KB,I,J):-I is lsb(KB),J is KB // (2^I).

n(x,0).
n((A>B),K):-n(A,I),n(B,J),cons(I,J,K).

t(0,x).
t(K,(A>B)):-K>0,decons(K,I,J),t(I,A),t(J,B).

parity(x,0).
parity(_>x,1).
parity(_>(X>Xs),P1):-parity(X>Xs,P0),P1 is 1-P0.

even_(_>Xs):-parity(Xs,1).
odd_(_>Xs):-parity(Xs,0).

s(x,x>x).
s(X>x,X>(x>x)):-!.
s(X>Xs,Z):-parity(X>Xs,P),s1(P,X,Xs,Z).

s1(0,x,X>Xs,SX>Xs):-s(X,SX).
s1(0,X>Ys,Xs,x>(PX>Xs)):-p(X>Ys,PX).
s1(1,X,x>(Y>Xs),X>(SY>Xs)):-s(Y,SY).
s1(1,X,Y>Xs,X>(x>(PY>Xs))):-p(Y,PY).

p(x>x,x).
p(X>(x>x),X>x):-!.
p(X>Xs,Z):-parity(X>Xs,P),p1(P,X,Xs,Z).

p1(0,X,x>(Y>Xs),X>(SY>Xs)):-s(Y,SY).
p1(0,X,(Y>Ys)>Xs,X>(x>(PY>Xs))):-p(Y>Ys,PY).
p1(1,x,X>Xs,SX>Xs):-s(X,SX).
p1(1,X>Ys,Xs, x>(PX>Xs)):-p(X>Ys,PX).

borrow(Op,X,Y,R):-n(X,A),n(Y,B),
  ArithOp=..[Op,A,B],C is ArithOp,t(C,R).
  
add(X,Y,R):-borrow((+),X,Y,R).
sub(X,Y,R):-borrow((-),X,Y,R).

rank(v(0),x).
rank(l(A),x>T):-rank(A,T).
rank(v(K),T>x):-K>0,t(K,T).
rank(a(A,B),X1>Y1):-
  rank(A,X),s(X,X1),
  rank(B,Y),s(Y,Y1).

unrank(x,v(0)).
unrank(x>T,l(A)):-!,unrank(T,A).
unrank(T>x,v(N)):-!,n(T,N).
unrank(X>Y,a(A,B)):-
  p(X,X1),unrank(X1,A),
  p(Y,Y1),unrank(Y1,B).

queryTypedTerm(L,QueryType,Term):-
  genTypedTerm(L,Term,QueryType),
  boundTypeOf(Term,QueryType).

queryTypedTerms(L,QueryType,Term):-
  genTypedTerms(L,Term,QueryType),
  boundTypeOf(Term,QueryType).

typeSiblingOf(Term,Sibling):-
  dbTermSize(Term,L),
  boundTypeOf(Term,Type),
  queryTypedTerms(L,Type,Sibling).

countForType(GivenType,M,Rs):-
  findall(R,
    (
       between(1,M,L),sols(queryTypedTerm(L,GivenType,_B),R)
    ),
  Rs).  

genTypedWithSomeFree(Size,NbFree,B,T):-
   between(0,NbFree,NbVs),
   length(FreeVs,NbVs),
   genTypedTerm(B,T,FreeVs,Size,0),
   bindTypeB(T).

typeCountsFor(L,T:Count):-
  setof(X,genTypedTerm(L,X,T),Xs),
  length(Xs,Count).
  
typeCountsUpTo(L,T:Count):-
  setof(X,genTypedTerms(L,X,T),Xs),
  length(Xs,Count).
  
popularTypesFor(L,K,[Difs,Sols,Ratio],PopularTs):-
  sols(genTypedTerm(L,_,_),Sols),
  setof(Count-T,typeCountsFor(L,T:Count),KTs),
  reverse(KTs,Sorted),
  take_(K,Sorted,PopularTs),
  length(KTs,Difs),
  Ratio is Difs/Sols.

popularTypesUpTo(L,K,[Difs,Sols,Ratio],PopularTs):-
  sols(genTypedTerms(L,_,_),Sols),
  setof(Count-T,typeCountsUpTo(L,T:Count),KTs),
  reverse(KTs,Sorted),
  take_(K,Sorted,PopularTs),
  length(KTs,Difs),
  Ratio is Difs/Sols.
  
take_(0,_Xs,[]):-!.
take_(_,[],[]):-!.
take_(N,[X|Xs],[X|Ys]):-N>0,N1 is N-1,take_(N1,Xs,Ys). 
 
 

genType --> genTree.
genTypes --> genTrees.

genByType(L,B,T):-
  genType(L,T),
  queryTypedTerms(L,T,B).

countByType(M,Rs):-
  findall(R,
    (
       between(1,M,L),sols(genByType(L,_B,_T),R)
    ),
  Rs).

ranTerm(Filter,Bits,T):-X is 2^Bits,N is X+random(X),M is N+X,
  between(N,M,I),
   unrankTerm(I,T),call(Filter,T),
  !.

ranOpen(Bits,T):-ranTerm(=(_),Bits,T).  

ranClosed(Bits,T):-ranTerm(isClosedC,Bits,T).

ranTyped(Bits,T):-ranTerm(closedTypable,Bits,T).

closedTypable(T):-isClosedC(T),typable(T).

genTypedSK(L,X,T):-genSK(L,X),simpleTypeOf(X,T).

genUntypableSK(L,X):-genSK(L,X),\+skTypeOf(X,_).

cat(0,1).
cat(N,R):-N>0, 
  PN is N-1,
  cat(PN,R1),
  R is 2*(2*N-1)*R1//(N+1).

countTyped(L,Typed,SKs,Prop):-
  sols(genTyped(L,_,_),Typed),
  cat(L,Cats),SKs is 2^(L+1)*Cats,
  Prop is Typed/SKs.
  
tcounts:-
  between(0,9,I),countTyped(I,Typed,All,Prop),
  write((I,&,Typed,&,All,&,Prop)),nl,fail.

genByTypeSK(L,X,T):-
  genType(L,T),
  genSKs(L,X),
  simpleTypeOf(X,T).

tsizeAll(V,R):-var(V),!,R=0.
tsizeAll(A,0):-atomic(A),!.
tsizeAll((X*Y),R):-tsizeAll(X,R1),tsizeAll(Y,R2),R is 1+R1+R2. 
tsizeAll((X>Y),R):-tsizeAll(X,R1),tsizeAll(Y,R2),R is 1+R1+R2. 

queryByTypeSK(L,X,T):-queryByType(X,T,L,0),simpleTypeOf(X,T).

queryByTypeSKs(L,X,T):-queryByType(X,T,L,_),simpleTypeOf(X,T).

queryByType(k,(A>(_B>A)))-->[]. 
queryByType(s,(((A>(B>C))> ((A>B)>(A>C)))))-->[].
queryByType((A*B),Y)-->
  down,
  queryByType(A,T),
  queryByType(B,X),
  {unify_with_occurs_check(T,(X>Y))}.

xgenByTypeSK(L,X,T):-
  genType(L,T),
  queryByTypeSKs(L,X,T).  

countByTypeSK(M,Rs):-
  findall(R,
    (
       between(1,M,L),sols(genByTypeSK(L,_B,_T),R)
    ),
  Rs).

wellTypedFrontier(Term,Trunk,FrontierEqs):-
  wtf(Term, Trunk,FrontierEqs,[]).

wtf(Term,X)-->{typableSK(Term)},!,[X=Term].
wtf(A*B,X*Y)-->wtf(A,X),wtf(B,Y).

fuseFrontier(FrontierEqs):-maplist(call,FrontierEqs).

extractFrontier(FrontierEqs,Frontier):-
  maplist(arg(2),FrontierEqs,Frontier).

simplifySK(Term,Trunk):-
  wellTypedFrontier(Term,Trunk,FrontierEqs),
  extractFrontier(FrontierEqs,Fs),
  maplist(evalSK,Fs,NormalizedFs),
  maplist(arg(1),FrontierEqs,Vs),
  Vs=NormalizedFs.

uselessTypeOf(k,(A>(_B>A))).
uselessTypeOf(s,(((A>(B>C))> ((A>B)>(A>C))))).
uselessTypeOf((A*B),Y):-
  uselessTypeOf(A,(X>Y)),
  uselessTypeOf(B,X).

notReallyTypable(X):-uselessTypeOf(X,_).

sameAsAny(L,M):-genSK(L,M),notReallyTypable(M).

iterType(K,X, Ts, Steps):-
  iterType(K,FinalK,X,[],Rs),
  reverse(Rs,Ts),
  Steps is K-FinalK.

iterType(K,FinalK,X,Xs,Ys):-K>0,K1 is K-1,
  xtype(X,T),
  \+(member(T,Xs)),
  !,
  iterType(K1,FinalK,T,[T|Xs],Ys).
iterType(FinalK,FinalK,_,Xs,Xs).


itersFrom(T,Size,Steps,Avg):-
  tsizeAll(T,Size),
  iterType(100,T,Ts0,Steps),
  Ts=[T|Ts0],
  maplist(tsizeAll,Ts,Sizes),
  avg(Sizes,Avg).

avg(Ns,Avg):-
  length(Ns,Len),
  sumlist(Ns,Sum),
  Avg is Sum/Len.

iterLens(M):-
  between(0,M,I),
  findall([Steps,AvgSize],(genTree(I,T),itersFrom(T,_Size,Steps,AvgSize)),Rs),
  % write(rs=Rs),nl,
  length(Rs,Len),
  foldl(msum,Rs,[0,0],Sums),
  maplist(divWith(Len),Sums,Avgs),
  write(avgs=[I|Avgs]),nl,
  fail.
  
msum([A,B],[D,E],[X,Y]):-
  X is A+D,Y is B+E.

  
msum([A,B,C],[D,E,F],[X,Y,Z]):-
  X is A+D,Y is B+E,Z is C+F.

divWith(X,Y,R):-R is Y / X.
    

iterTo(M):-
  between(0,M,I),
  t(I,T),tsizeAll(T,Size),
  iterType(100,T,Ts,Steps),
  maplist(tsizeAll,Ts,Sizes),
  length(Sizes,Len),
  sumlist(Sizes,Sum),
  Avg is Sum / Len,
  write((I,Steps,Size,Avg)),
  nl,
  fail.

genSelfTypedT(L,T):-genTree(L,T),xtype(T,T).

countSelfTypedT(M,Rs):-
  findall(R,
    (
       between(1,M,L),sols(genSelfTypedT(L,_T),R)
    ),
  Rs).  

b2b --> rank,t2b.
t2t --> t2b,rank.

evalOrNextB(B,EvB):-boundTypeOf(B,_),evalDeBruijn(B,EvB),EvB\==B,!.
evalOrNextB(B,NextB):-
  rank(B,T),
  s(T,NextT),
  unrank(NextT,NextB).

playWithB(Term,Steps,Orbit):-
  playWithB(Term,Steps,Orbit,[]).

playWithB(Term,Steps,[NewTerm|Ts1],Ts2):-Steps>0,!,
  Steps1 is Steps-1,
  evalOrNextB(Term,NewTerm),
  playWithB(NewTerm,Steps1,Ts1,Ts2).
playWithB(Term,_,[Term|Ts],Ts).

evalOrNextT(T,EvT):-xtype(T,_),evalX(T,EvT),EvT\==T,!.
evalOrNextT(T,NextT):-s(T,NextT).

playWithT(Term,Steps,Orbit):-playWithT(Term,Steps,Orbit,[]).

playWithT(Term,Steps,[NewTerm|Ts1],Ts2):-Steps>0,!,
  Steps1 is Steps-1,
  evalOrNextT(Term,NewTerm),
  playWithT(NewTerm,Steps1,Ts1,Ts2).
playWithT(Term,_,[Term|Ts],Ts).

t2p(T,Ps):-t2p(T,0,1,Ps,[]).

t2p(X,L,R) --> [L],t2ps(X,L,R).

t2ps(x,_,R) --> [R].
t2ps((X>Xs),L,R) --> t2p(X,L,R),t2ps(Xs,L,R). 

% generators
ttsizes:-
 between(0,1000,N),t(N,T),t2t(T,TT),tsizeAll(T,S1),
 tsizeAll(TT,S2),write((N,S1,S2)),nl,fail.
 
nonetyped:-
  between(0,10000,N),t(N,T),t2t(T,TT),xtype(TT,_),
  write(N),nl,fail.
 
closedTo(M,I,B):-
  between(0,M,I),
  t(I,T),
  unrank(T,B),
  isClosedB(B).

typedTo(M,I,B,T):-
  between(0,M,I),
  t(I,T),
  unrank(T,B),
  isClosedB(B),
  boundTypeOf(B,T).
 
ttyped(From,To,I,TT):-between(From,To,I),t(I,T),t2b(T,B),boundTypeOf(B,TT). 

bclosed(From,To,I):-between(From,To,I),t(I,T),unrank(T,B),isClosedB(B).

% counts

ccount(M,R):-sols(closedTo(M,_,_),R).

tcount(M,R):-sols(typedTo(M,_,_,_),R). 

tcount1(M,R):-sols(ttyped(M,_I,_TT),R). 
  
% 22527 first non-stopping evalDeBruijn
    

binDif(N,X,Y,R):- N1 is 2*N-X,R1 is N - (X + Y) // 2, R2 is R1-1,
  binomial(N1,R1,B1),binomial(N1,R2,B2),R is B1-B2.  

localRank(N,As,NewLo):- X is 1, Y is 0, Lo is 0,
  binDif(N,0,0,Hi0),Hi is Hi0-1,
  localRankLoop(As,N,X,Y,Lo,Hi,NewLo,_NewHi).

localRankLoop(As,N,X,Y,Lo,Hi,FinalLo,FinalHi):-N2 is 2*N,X< N2,!,
  PY is Y-1, SY is Y+1, nth0(X,As,A),
  (0=:=A-> binDif(N,X,PY,Hi1),
     NewHi is Hi-Hi1, NewLo is Lo, NewY is SY
   ; binDif(N,X,SY,Lo1),
     NewLo is Lo+Lo1, NewHi is Hi, NewY is PY
  ), NewX is X+1,
  localRankLoop(As,N,NewX,NewY,NewLo,NewHi,FinalLo,FinalHi).
localRankLoop(_As,_N,_X,_Y,Lo,Hi,Lo,Hi).  

rankLoop(I,S,FinalS):-I>=0,!,cat(I,C),NewS is S+C, PI is I-1,
  rankLoop(PI,NewS,FinalS).
rankLoop(_,S,S).

localUnrank(N,R,As):-Y is 0,Lo is 0,binDif(N,0,0,Hi0),Hi is Hi0-1, X is 1,
  localUnrankLoop(X,Y,N,R,Lo,Hi,As).

localUnrankLoop(X,Y,N,R,Lo,Hi,As):-N2 is 2*N,X=<N2,!,
   PY is Y-1, SY is Y+1,
   binDif(N,X,SY,K), LK is Lo+K,
   ( R<LK -> NewHi is LK-1, NewLo is Lo, NewY is SY, Digit=0
   ; NewLo is LK, NewHi is Hi, NewY is PY, Digit=1
   ),nth0(X,As,Digit),NewX is X+1,
   localUnrankLoop(NewX,NewY,N,R,NewLo,NewHi,As).
localUnrankLoop(_X,_Y,_N,_R,_Lo,_Hi,_As). 

unrankLoop(R,S,I,FinalS,FinalI):-cat(I,C),NewS is S+C, NewS=<R,
   !,NewI is I+1,
   unrankLoop(R,NewS,NewI,FinalS,FinalI).
unrankLoop(_,S,I,S,I).

list2set(Ns,Xs) :- list2set(Ns,-1,Xs).

list2set([],_,[]).
list2set([N|Ns],Y,[X|Xs]) :- 
  X is (N+Y)+1, 
  list2set(Ns,X,Xs).

set2list(Xs,Ns) :- set2list(Xs,-1,Ns).

set2list([],_,[]).
set2list([X|Xs],Y,[N|Ns]) :- 
  N is (X-Y)-1, 
  set2list(Xs,X,Ns).

binomialLoop(_,K,I,P,R) :- I>=K, !, R=P.
binomialLoop(N,K,I,P,R) :- I1 is I+1, P1 is ((N-I)*P) // I1,
   binomialLoop(N,K,I1,P1,R).

binomial(_N,K,R):- K<0,!,R=0.
binomial(N,K,R) :- K>N,!, R=0.
binomial(N,K,R) :- K1 is N-K, K>K1, !, binomialLoop(N,K1,0,1,R).
binomial(N,K,R) :- binomialLoop(N,K,0,1,R).

% helpers

nv(X):-numbervars(X,0,_).

pn(X):-numbervars(X,0,_),write(X),nl,fail.
pn(_).

lb(B):-b2l(B,T),lamshow(T),nl. 
tb(B):-b2l(B,T),texshow(T),nl. 

lx(X):-c2b(X,B),b2l(B,T),lamshow(T),nl. 
tx(X):-c2b(X,B),b2l(B,T),texshow(T),nl. 

lamshow(T):-
  numbervars(T,0,_),
  lamshow(T,Cs,[]),
  maplist(write,Cs),
  fail.
lamshow(_).

lamshow('$VAR'(I))--> [x],[I].
lamshow(l('$VAR'(I),E))-->[('(')],[('\\')],[x],[I],[('.')],lamshow(E),[(')')].
lamshow(a(X,Y))-->[('(')],lamshow(X),[(' ')],lamshow(Y),[(')')].

texshow(T):-
  numbervars(T,0,_),
  texshow(T,Cs,[]),
  maplist(write,Cs),
  fail.
texshow(_).

texshow('$VAR'(I))--> [x],['_'],[I].
texshow(l('$VAR'(I),E))-->[(' ')],[('~\\lambda ')],[x], ['_'],   [I],[('.')],texshow(E),[(' ')].
texshow(a(X,Y))-->[('(')],texshow(X),[('~')],texshow(Y),[(')')].

% counts nb. of solutions of Goal 
sols(Goal, Times) :-
        Counter = counter(0),
        (   Goal,
            arg(1, Counter, N0),
            N is N0 + 1,
            nb_setarg(1, Counter, N),
            fail
        ;   arg(1, Counter, Times)
        ).

count1(F,M,Ks):-findall(K,(between(0,M,L),sols(call(F,L),K)),Ks).

count2(F,M,Ks):-findall(K,(between(0,M,L),sols(call(F,L,_),K)),Ks).

count3(F,M,Ks):-findall(K,(between(0,M,L),sols(call(F,L,_,_),K)),Ks).


