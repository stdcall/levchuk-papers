# Lemma4, printed511–512. Complete subgroup enumeration in PSL2(q)
# for the explicitly listed finite fields, not the infinite-field theorem.
# The projective action retains the distinction SL2 versus PSL2.
SetAssertionLevel(1);
checks := 0;
RunChecks := function()
local q,F,z,o,S,points,action,G,x,y,Xone,tested,exceptional2,
      exceptional3,cl,H,V,W;
for q in [2,3,4,5,7,8,9] do
    F := GF(q);;
    z := Zero(F);; o := One(F);;
    S := SL(2,q);;
    points := Orbit(S,[o,z],OnLines);;
    action := ActionHomomorphism(S,points,OnLines);;
    G := Image(action);;
    x := t -> [[o,t],[z,o]];
    y := t -> [[o,z],[t,o]];
    Xone := Image(action,x(o));;
    tested := 0;; exceptional2 := 0;; exceptional3 := 0;;
    for cl in ConjugacyClassesSubgroups(G) do
        for H in AsList(cl) do
            if not Xone in H then continue; fi;
            V := Filtered(Elements(F),t -> Image(action,x(t)) in H);;
            W := Filtered(Elements(F),t -> Image(action,y(t)) in H);;
            if Length(W)=1 then continue; fi;
            tested := tested+1;
            Assert(1,ForAll(V,a -> ForAll(V,b -> a+b in V and a*b in V)));
            Assert(1,ForAll(V,a -> a=z or a^-1 in V));
            checks := checks+2;
            Assert(1,ForAny(Filtered(Elements(F),t -> t<>z),
                t -> Image(action,[[z,t],[-t^-1,z]]) in H));
            checks := checks+1;
            if Set(W)<>Set(V) then
                if Length(V)=3 then
                    Assert(1,ForAny(Elements(F),i -> i^2=-o
                        and Set(List(V,a -> i*a))=Set(W)));
                    exceptional3 := exceptional3+1;
                else
                    Assert(1,Length(V)=2 and Length(W)=2);
                    exceptional2 := exceptional2+1;
                fi;
                checks := checks+1;
            fi;
        od;
    od;
    Print("q=",q," PSL2-order=",Size(G)," tested=",tested,
          " exceptional |V|2=",exceptional2," |V|3=",exceptional3,"\n");
od;
end;
RunChecks();
Print("ok l1983-root-periodic-rank-one: ",checks," checks GAP",
      GAPInfo.Version,"\n");
QUIT;
