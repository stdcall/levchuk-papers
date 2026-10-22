# Finite checks of pp.425–433; not a proof over all fields.
SetAssertionLevel(1);
checks := 0;
Check := function(value)
    Assert(1,value);
    checks := checks+1;
end;
RunFinite := function()
local q,F,o,z,S,points,action,G,x,y,diag,H,cl,V,T,A,A2,Vstar,f,
      normaldihedral,subgroups,casecount,unipotentfree,p,N;
for q in [2,3,4,5,7,8,9,11] do
    F:=GF(q); o:=One(F); z:=Zero(F); p:=Characteristic(F);
    S:=SL(2,q);
    points:=Orbit(S,[o,z],OnLines);
    action:=ActionHomomorphism(S,points,OnLines);
    G:=Image(action);
    x:=t -> [[o,t],[z,o]];
    y:=t -> [[o,z],[t,o]];
    diag:=t -> [[t,z],[z,t^-1]];
    casecount:=0; unipotentfree:=0;
    for cl in ConjugacyClassesSubgroups(G) do
        H:=Representative(cl);
        if Size(H) mod p<>0 then
            # Lemma4: a cyclic normal subgroup of index<=2 is a
            # diagonalizable one, since its order is prime to p.
            normaldihedral:=ForAny(NormalSubgroups(H),
                N -> IsCyclic(N) and Index(H,N)<=2);
            Check(normaldihedral or IdGroup(H) in [[12,3],[24,12],[60,5]]);
            unipotentfree:=unipotentfree+1;
        fi;
        for H in AsList(cl) do
            if not Image(action,x(o)) in H then continue; fi;
            if not ForAny(Filtered(Elements(F),t -> t<>z),
                    t -> Image(action,y(t)) in H) then continue; fi;
            casecount:=casecount+1;
            V:=Filtered(Elements(F),t -> Image(action,x(t)) in H);
            Vstar:=Filtered(V,t -> t<>z);
            T:=Stabilizer(H,Position(points,[z,o]));
            # A is the DIAGONAL PROJECTION of T, defined in p.426 by
            # T*tau_F=tau_F semidirect delta_A. It is not T inter delta.
            # The exceptional A5 complement is shifted by a translation.
            A:=Filtered(Filtered(Elements(F),t -> t<>z),
                        t -> ForAny(Elements(F),a ->
                            Image(action,x(a)*diag(t)) in H));
            A2:=Set(List(A,t -> t^2));
            f:=(Index(H,T)-1)/Length(V);
            Check(IsInt(f) and f>=1);
            Check(Set(A)=Set(Vstar) or A2=Set(Vstar));
            if Length(V)=2 then
                Check(IsDihedralGroup(H));
            elif Set(A)=Set(Vstar) then
                Check(Size(H)=Length(V)*(Length(V)^2-1)
                                  /Gcd(2,Length(V)-1));
                Check(f=1);
            elif f=1 then
                Check(Size(H)=Length(V)*(Length(V)^2-1));
            else
                Check(Length(V)=3 and f=3 and IdGroup(H)=[60,5]);
            fi;
            if Length(V)>2 and Set(A)=Set(Vstar) then
                # Lemma8в: each non-triangular right coset has q-1
                # unipotents. In odd characteristic exactly one lift
                # has trace2, so count projective elements via order p.
                Check(ForAll(RightCosets(H,T), C ->
                    Representative(C) in T or
                    Number(AsList(C),g -> Order(g)=p)=Length(V)-1));
            fi;
        od;
    od;
    Print("q=",q," normalized cases=",casecount,
          " p-free conjugacy representatives=",unipotentfree,"\n");
od;
end;
RunFinite();

RunExceptional := function()
local F,o,z,i,U,L,W,gamma,S,points,act,u,w,g,H,j,omega,v,
      fp,x,y,c,corrected;
F:=GF(9); o:=One(F); z:=Zero(F);
i:=First(Elements(F),t -> t^2=-o);
U:=[[o,o],[z,o]]; L:=[[o,z],[o,o]];
W:=[[z,o],[-o,z]]; gamma:=[[i,o],[z,-i]];
S:=SL(2,9); points:=Orbit(S,[o,z],OnLines);
act:=ActionHomomorphism(S,points,OnLines);
u:=Image(act,U); w:=Image(act,W); g:=Image(act,gamma);
H:=Group(u,w,g);
Check(Size(H)=60 and IdGroup(H)=[60,5]);
Check(Order(u)=3 and Order(w)=2 and Order(g)=2);
Check((u*w)^3=One(H) and (w*g)^3=One(H) and (u*g)^2=One(H));
# Keep the printed reading as an explicitly refuted check.
Check(w^3<>One(H));
fp:=FreeGroup("u","w","g"); x:=fp.1; y:=fp.2; c:=fp.3;
corrected:=fp/[x^3,y^2,c^2,(x*y)^3,(y*c)^3,(x*c)^2];
Check(Size(corrected)=60 and IdGroup(corrected)=[60,5]);
Print("corrected Moore presentation order=",Size(corrected),"\n");
# Second exceptional realization, pp.429–430: i²=-1 and the five
# factors have trace0. Both triangle relations are projective.
v:=Image(act,[[o,z],[i,o]]);
omega:=u*v*u*v*u;
Check(Order(omega)=2 and Order(u*omega)=5);
Check(Size(Group(u,omega))=60);
Check(omega*u*omega=v);
end;
RunExceptional();
# Every explicit permutation product used in p.429, in GAP's usual
# right-action convention, which agrees with these printed products.
sigma:=(1,2,3); pi:=(2,3,4);
theta1:=(1,2)(4,5); theta2:=(1,3)(4,5); theta3:=(2,3)(4,5);
Check(sigma*pi=(1,3)(2,4));
Check(pi*theta1*sigma^-1=(3,5,4));
Check(pi*theta2*sigma=(3,5,4));
Check(pi*theta3=(3,5,4));
pi:=(3,4,5);
Check(sigma*pi*sigma*pi*sigma=(1,4)(2,5));
Print("ok l1983-dickson-finite: ",checks," checks GAP",GAPInfo.Version,"\n");
QUIT;
