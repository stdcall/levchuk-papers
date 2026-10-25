# Exhaustive characteristic-subgroup calculation for U(C2,GF(4)).
# Matrices use symplectic basis e1,e2,f1,f2, as in the companion Sage file.
# This checks one concrete group, not a general replacement count.
f := GF(4);;
z := Z(4);;
one := IdentityMat(4,f);;
a := NullMat(4,4,f);; a[1][2] := One(f);; a[4][3] := One(f);;
b := NullMat(4,4,f);; b[2][4] := One(f);;
c := NullMat(4,4,f);; c[1][4] := One(f);; c[2][3] := One(f);;
d := NullMat(4,4,f);; d[1][3] := One(f);;
gens := [];;
for r in [a,b,c,d] do
  for t in [One(f),z] do Add(gens,one+t*r); od;
od;
g := Group(gens);;
if Size(g) <> 256 then Error("wrong matrix group order"); fi;
iso := IsomorphismPcGroup(g);;
p := Image(iso);;
cc := CharacteristicSubgroups(p);;
sizes := SortedList(List(cc,Size));;
if sizes <> [1,16,256] then Error("unexpected characteristic orders: ",sizes); fi;
if Length(cc) = 7 then Error("printed count unexpectedly true"); fi;
Print("ok l1996-c2-characteristic-gap: order ",Size(g),
      "; characteristic subgroup orders ",sizes,"; printed count 7 refuted\n");
QUIT_GAP(0);
