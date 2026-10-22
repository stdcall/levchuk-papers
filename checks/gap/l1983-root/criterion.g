# Rank-one part of section 4, including its two small-field exceptions.
# All additive-subgroup pairs are checked in the named finite fields.
# Matrices are saturated by the scalar centre before root intersections
# are taken, so the test is in PSL(2,q), as required by the article.
# This finite check does not prove the arbitrary-field or higher-rank
# criterion, nor the classification theorem for twisted groups.
checks := 0;; pairs := 0;; failuresOfUnconditionalClaim := 0;;
H := fail;; F := fail;;
Check := function(test, message)
  if not test then
    Print("FAIL l1983-root criterion: ",message,"\n");
    QUIT_GAP(1);
  fi;
  checks := checks + 1;
end;;
Upper := function(t)
  local o,z; o:=One(t); z:=Zero(t);
  return [[o,t],[z,o]];
end;;
Lower := function(t)
  local o,z; o:=One(t); z:=Zero(t);
  return [[o,z],[t,o]];
end;;
Predict := function(A,B,F)
  local t,u,P,c;
  for t in Difference(A,[Zero(F)]) do
    P:=Set(List(A,x->x/t));
    if One(F) in P and ForAll(P,x->ForAll(P,y->x*y in P)) then
      for u in Difference(B,[Zero(F)]) do
        if Set(List(B,x->x/u))=P then
          c:=t*u;
          if c in P or Length(P)=2 or
             (Length(P)=3 and c^2=-One(F)) then return true; fi;
        fi;
      od;
    fi;
  od;
  return false;
end;;
for q in [4,8,9] do
  F:=GF(q);;
  additive:=Filtered(Combinations(Elements(F)),A->Length(A)>1 and
    Zero(F) in A and ForAll(A,x->ForAll(A,y->x+y in A)));;
  for A in additive do for B in additive do
    generators:=Concatenation(List(A,Upper),List(B,Lower),[-IdentityMat(2,F)]);;
    H:=Group(generators);;
    actualA:=Filtered(Elements(F),x->Upper(x) in H);;
    actualB:=Filtered(Elements(F),x->Lower(x) in H);;
    admissible:=(Set(actualA)=Set(A) and Set(actualB)=Set(B));;
    Check(admissible=Predict(A,B,F),"rank-one criterion mismatch");
    pairs:=pairs+1;
    if not admissible then
      failuresOfUnconditionalClaim:=failuresOfUnconditionalClaim+1;
    fi;
  od; od;
od;
# Explicit counterexample to unrestricted admissibility in remark 2:
# A is the whole additive GF(4), B is its prime field GF(2).
# A1 has no non-proportional root pairs, so every pair is an elementary
# carpet, but here the generated group enlarges its negative root group.
F:=GF(4);; A:=Elements(F);; B:=[Zero(F),One(F)];;
H:=Group(Concatenation(List(A,Upper),List(B,Lower)));;
Check(Lower(Z(4)) in H,"explicit nonadmissible carpet not detected");
Check(not Z(4) in B,"counterexample parameter already in B");
# Embed the same example into the A1 root subsystem of type A2.
Embed := function(m)
  return [[m[1][1],m[1][2],Zero(F)],
          [m[2][1],m[2][2],Zero(F)],
          [Zero(F),Zero(F),One(F)]];
end;;
H3:=Group(Concatenation(List(A,x->Embed(Upper(x))),
                       List(B,x->Embed(Lower(x)))));;
Check(Embed(Lower(Z(4))) in H3,"A2 embedded counterexample");
# Explicit order-three exception: P=GF(3), i^2=-1 in GF(9).
F:=GF(9);; P:=Elements(GF(3));; i:=First(Elements(F),x->x^2=-One(F));;
Check(i<>fail and not i in P,"missing exceptional scalar");
A:=P;; B:=Set(List(P,x->i*x));;
H:=Group(Concatenation(List(A,Upper),List(B,Lower),[-IdentityMat(2,F)]));;
Check(Set(Filtered(Elements(F),x->Upper(x) in H))=Set(A),"exception A");
Check(Set(Filtered(Elements(F),x->Lower(x) in H))=Set(B),"exception B");
Check(Size(H)/Size(Centre(H))=60,"exceptional projective order is not 60");
Check(failuresOfUnconditionalClaim>0,"no counterexamples found");
Print("ok l1983-root criterion: ",checks," checks; ",pairs,
      " additive pairs; ",failuresOfUnconditionalClaim,
      " nonadmissible pairs; GAP ",GAPInfo.Version,"\n");
QUIT_GAP(0);
