#############################################################################
##
#A  fpgtorws4.g                  GAP library                  Derek Holt
##
##  This file contains a function to calculate a rewriting-system from
##  a finitely presented group.
##  It is derived from such a function for group presentations
##  written by Werner Nickel.
##
##
#############################################################################
##
#F  FpGroupToRWS(<G>). calculate a rewriting-system for group G
##
##  <G> must be a finitely presented group. This function calculates and
##  returns a rewriting-system for <G>.
##
##  Public function.
FpGroupToRWS := function ( G )
    local    F, rws, gens, invgens, ggens,
             mnames, grels, lhs, rhs, g, l, hl, ng, r, i, j, k, ct,
             gtom,  igtom;

    # check the given argument to be an fp-group.
    if not IsFpGroup(G) then
       Error("Argument must be a finitely presented group");
    fi;

    rws := rec();
    rws.GpMonSgp := G;
    rws.hasOne := true;
    F:=FreeGroupOfFpGroup(G);
    rws.FreeGpMonSgp := F;
    rws.options := rec();

    rws.alphabet := [];
    rws.invAlphabet := [];
    invgens := rws.invAlphabet;
    rws.ordering := "shortlex";
    
    ggens := GeneratorsOfGroup(F);
    ng := Length(ggens);
    grels:=ShallowCopy(RelatorsOfFpGroup(G));

    mnames := [];
    gtom:=[];
    igtom:=[];
    ct := 0;
    for i in [1..ng] do
       ct := ct+1;
       Add(mnames,Concatenation("_g",String(ct)));
       Add(gtom,ct);
       #Check to see if this generator is involutory.
       #If so, remove all occurrences of its inverse from the relators.
       #If not, adjoin an inverse generator to gens.
       if Position(grels,ggens[i]^2)<>fail or
          Position(grels,ggens[i]^-2)<>fail  then
          for j in [1..Length(grels)] do
             k := 1;
             while k <= Length(grels[j]) do
                if Subword(grels[j],k,k)=ggens[i]^-1 then
                   grels[j] := SubstitutedWord(grels[j],k,k,ggens[i]);
                   k := 1;
                else k := k+1;
                fi;
             od;
          od;
          Add(rws.invAlphabet,ct);
          Add(igtom,ct);
       else
         ct := ct+1;
         Add(mnames,Concatenation("_g",String(ct)));
         Append(rws.invAlphabet,[ct,ct-1]);
         Add(igtom,ct);
       fi;
    od;

    ng := ct;
    rws.WordMonoid := FreeMonoid(mnames);
    rws.ExtIntCorr := CorrespondenceGroupMonoid(F,rws.WordMonoid,gtom,igtom);
    rws.ExtToInt := FreeGroup2FreeMonoid;
    rws.IntToExt := FreeMonoid2FreeGroup;
    gens := GeneratorsOfMonoid(rws.WordMonoid);
    rws.alphabet := gens;

    rws.equations := [];
    for r in grels do
       if r <> One(F) then
         #balance the equation
         l := Length(r); hl := Int((l+1)/2);
         lhs := Subword(r,1,hl); rhs := Subword(r,hl+1,l)^-1;
         lhs := FreeGroup2FreeMonoid(rws.ExtIntCorr,lhs);
         rhs := FreeGroup2FreeMonoid(rws.ExtIntCorr,rhs);
         if lhs <> rhs then
             Add(rws.equations,[WordToListRWS(lhs,gens),
                            WordToListRWS(rhs,gens)]);
         fi;
       fi;
    od;

    return rws;
end;

#############################################################################
##
#F  FpMonoidToRWS(<S>). . . calculate a rewriting-system for monoid S
##
##  <S> must be a finitely presented monoid. This function calculates and
##  returns a rewriting-system for <S>.
##
##  Public function.
FpMonoidToRWS := function ( S )
    local    rws, gens, rels, ng, r, i, mnames, F, r1, r2;

    # check the given argument to be an fp-group.
    if not IsFpMonoid(S) then
       Error("Argument must be a finitely presented monoid");
    fi;

    rws := rec();
    rws.GpMonSgp := S;
    rws.hasOne := true;
    F:=FreeMonoidOfFpMonoid(S);
    rws.FreeGpMonSgp := F;
    rws.options := rec();

    rws.ordering := "shortlex";
    ng := Length(GeneratorsOfMonoid(F));
    mnames := [];
    for i in [1..ng] do
      mnames[i] := Concatenation("_m",String(i));
    od;
    rws.WordMonoid := FreeMonoid(mnames);
    rws.ExtIntCorr := CorrespondenceMSMonoid(F,rws.WordMonoid);
    rws.ExtToInt := FreeMS2FreeMonoid;
    rws.IntToExt := FreeMonoid2FreeMS;

    gens := GeneratorsOfMonoid(rws.WordMonoid);
    rws.alphabet := gens;
    rws.invAlphabet := List([1..ng],i->false);
    
    rels:=RelationsOfFpMonoid(S);
    rws.equations := [];
    for r in rels do
      if r[1] <> r[2] then
         r1 := FreeMS2FreeMonoid(rws.ExtIntCorr,r[1]);
         r2 := FreeMS2FreeMonoid(rws.ExtIntCorr,r[2]);
         Add(rws.equations,[WordToListRWS(r1,gens),
                            WordToListRWS(r2,gens)]);
      fi;
    od;

    return rws;
end;

#############################################################################
##
#F  FpSemigroupToRWS(<S>). . . calculate a rewriting-system for semigroup S
##
##  <S> must be a finitely presented semigroup. This function calculates and
##  returns a rewriting-system for <S>.
##
##  Public function.
FpSemigroupToRWS := function ( S )
    local    rws, gens, rels, ng, r, i, mnames, F, r1, r2;

    # check the given argument to be an fp-group.
    if not IsFpSemigroup(S) then
       Error("Argument must be a finitely presented semigroup");
    fi;

    rws := rec();
    rws.GpMonSgp := S;
    rws.hasOne := false;
    F:=FreeSemigroupOfFpSemigroup(S);
    rws.FreeGpMonSgp := F;
    rws.options := rec();

    rws.ordering := "shortlex";
    
    ng := Length(GeneratorsOfSemigroup(F));
    mnames := [];
    for i in [1..ng] do
      mnames[i] := Concatenation("_s",String(i));
    od;
    rws.WordMonoid := FreeMonoid(mnames);
    rws.ExtIntCorr := CorrespondenceMSMonoid(F,rws.WordMonoid);
    rws.ExtToInt := FreeMS2FreeMonoid;
    rws.IntToExt := FreeMonoid2FreeMS;

    gens := GeneratorsOfMonoid(rws.WordMonoid);
    rws.alphabet := gens;
    rws.invAlphabet := List([1..ng],i->false);
    
    rels:=RelationsOfFpSemigroup(S);
    rws.equations := [];
    for r in rels do
      if r[1] <> r[2] then
         r1 := FreeMS2FreeMonoid(rws.ExtIntCorr,r[1]);
         r2 := FreeMS2FreeMonoid(rws.ExtIntCorr,r[2]);
         Add(rws.equations,[WordToListRWS(r1,gens),
                            WordToListRWS(r2,gens)]);
      fi;
    od;

    return rws;
end;
