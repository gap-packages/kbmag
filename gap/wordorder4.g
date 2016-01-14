InfoStoreBetterDHVtx := Ignore;
InfoUpdateHistory := Ignore;
InfoUpdateTriple :=Ignore;
InfoReductionDH := Ignore;
InfoReductionHistory := Ignore;
InfoDiffHistoryVtx := Ignore;
InfoDiffReducedWord := Ignore;
InfoDiffReducedWord2 := Ignore;
InfoSubstringClosure := Ignore;
InfoWdAcceptor := Print;
InfoCorrectDiffMachine := Ignore;
InfoCorrectDiffMachine2 := Ignore;
InfoTestAutomatic := Ignore;

WordOrder := function(arg)
  local type, generators,invAlphabet, weight, level, maxLevel, getWeight,
    history, updateHistory, reductionHistory, betterThanHistory,
    F,i,monoidGenerators, IdWord;

  # Because GAP freely reduces words as it multiplies them, I have
  # made a second set of generators, the monoidGenerators. When
  # I need to make words which aren't freely reduced, I use those.
  # When GAP stops freely reducing words during multiplication,
  # all occurrences of monoidGenerators can be replaced by
  # generators - SR
  
  if IsKBMAGRewritingSystemRep(arg[1]) then
    generators := arg[1]!.alphabet;
    invAlphabet := arg[1]!.invAlphabet;
    type := arg[1]!.ordering;
    if type="wtlex" or type="wtshortlex" then weight := arg[1]!.weight; 
    elif type="wreathprod" then level := arg[1]!.level; 
    fi;
  elif IsGroup(arg[1]) then
    type := arg[2];
    generators := [];
    invAlphabet := [];
    for i in [1..Length(arg[2].alphabet)] do
      generators[2*i-1] := arg[2].alphabet[i];
      invAlphabet[2*i] := arg[2].alphabet[i];
      generators[2*i] := arg[2].alphabet[i]^-1;
      invAlphabet[2*i-1] := arg[2].alphabet[i]^-1;
    od;
    if type="wtlex" or type="wtshortlex" then weight := arg[3]; 
    elif type="wreathprod" then level := arg[3]; 
    fi;
  fi;

  F := FreeGroup(Length(generators));
  monoidGenerators := ShallowCopy(GeneratorsOfGroup(F));
  IdWord := One(F);
   
  if type="wtlex" or type="wtshortlex" then 
    getWeight := function(w)
     local wt,i;

      wt:= 0;
      for i in [1..Length(w)] do
        wt := wt + weight[Position(generators,Subword(w,i,i))];
      od;
      return wt;
    end;
  elif type="wreathprod" then
    maxLevel := 0;
    for i in [1..Length(level)] do
      if level[i]>maxLevel then maxLevel := level[i]; fi;
    od;

    history := function(g,h)
      local longer, lev_v, lev_u, seq;
      seq := [];
      lev_v:= level[g];
      if h=0 then 
        longer:=1;
        lev_u := 0;
        seq[lev_v] := [0,monoidGenerators[g],IdWord]; 
      else
        longer:=0;
        lev_u := level[h];
        if level[g]=level[h] then 
          if (g>h) then seq[lev_v] := [1,IdWord,IdWord]; 
          else seq[lev_v] := [-1,IdWord,IdWord]; # g and h cannot be equal
          fi;
        else
          seq[lev_v] := [0,monoidGenerators[g],IdWord]; 
          seq[lev_u] := [0,IdWord,monoidGenerators[h]]; 
        fi;
      fi;
      return rec(longer:= longer,lev_v:=lev_v,lev_u:=lev_u,seq:=seq);
    end;

    updateHistory := function(oldHist,g,h,N)
      local hist, longer,lev_v,lev_u,seq,
         outOfBounds, foundInt, j,
         updateTriple;

      InfoUpdateHistory("Entering updateHistory with ",
                                   oldHist," ",g," ",h,"\n");
      # this function is local to updateHistory
      updateTriple := function(oldTriple,g,h) 
        # Either g or h might be zero, but not both,
        # these may not both be the g and h in the argument set of 
        # updateHistory
        # If non-zero, g or h has the right level for the triple.
        local oldC, oldV2, oldU2, c,v2,u2,gg,hh;

        InfoUpdateTriple("Entering updateTriple with ",
             oldTriple," ",g," ",h,"\n");
        oldC := oldTriple[1];
        oldV2 := oldTriple[2];
        oldU2 := oldTriple[3];
        if Length(oldV2) = 0 and g=0 then
          InfoUpdateTriple("Leaving updateTriple with ",
             " ",oldC," ",IdWord," ",oldU2*monoidGenerators[h],"\n");
          return [oldC,IdWord,oldU2*monoidGenerators[h]];
        elif Length(oldU2) = 0 and h=0 then
          InfoUpdateTriple("Leaving updateTriple with ",
             " ",oldC," ",oldV2*monoidGenerators[g]," ",IdWord,"\n");
          return [oldC,oldV2*monoidGenerators[g],IdWord];
        fi;
        if Length(oldV2) = 0 then
          gg := g;
          v2 := IdWord;
        elif Length(oldV2) = 1 then
          gg := Position(monoidGenerators,Subword(oldV2,1,1));
          if g<> 0 then v2 := monoidGenerators[g];
          else v2 := IdWord; fi;
        else
          gg := Position(monoidGenerators,Subword(oldV2,1,1));
          if g<> 0 then
            v2 := Subword(oldV2,2,Length(oldV2))*monoidGenerators[g];
          else
            v2 := Subword(oldV2,2,Length(oldV2));
          fi;
        fi;
        if Length(oldU2) = 0 then
          hh := h;
          u2 := IdWord;
        elif Length(oldU2) = 1 then
          hh := Position(monoidGenerators,Subword(oldU2,1,1));
          if h<> 0 then u2 := monoidGenerators[h];
          else u2 := IdWord; fi;
        else
          hh := Position(monoidGenerators,Subword(oldU2,1,1));
          if h<> 0 then
            u2 := Subword(oldU2,2,Length(oldU2))*monoidGenerators[h];
          else
            u2 := Subword(oldU2,2,Length(oldU2));
          fi;
        fi;
        if oldC=0 and gg>hh then c:= 1;
        elif oldC=0 and gg<hh then c:= -1;
        else c := oldC;
        fi;
        InfoUpdateTriple("Leaving updateTriple with ",
             " ",c," ",v2," ",u2,"\n");
        return [c,v2,u2];
      end;

      if oldHist.longer=1 and h<>0 then return []; fi; 
      seq := ShallowCopy(oldHist.seq);

      if g=0 or level[g]<oldHist.lev_v then lev_v := oldHist.lev_v; 
        # we allow g=0 only during lookahead for reduction - i.e. such
        # histories don't get stored 
      else lev_v := level[g]; 
      fi;
      if h=0 or level[h]<oldHist.lev_u then lev_u := oldHist.lev_u; 
      else lev_u := level[h];
      fi;

      if h=0 then 
        longer:=1;
        if lev_v=level[g] then
          if not IsBound(oldHist.seq[lev_v]) then
            seq[lev_v] := [0,monoidGenerators[g],IdWord];
          elif IsList(oldHist.seq[lev_v]) then
            seq[lev_v] := updateTriple(oldHist.seq[lev_v],g,h);
          fi;
        fi; # if g has level less than lev_v nothing gets changed
      elif g=0 then 
        longer:= -1;
        if lev_u=level[h] then
          if not IsBound(oldHist.seq[lev_u]) then
            seq[lev_u] := [0,IdWord,monoidGenerators[h]];
          elif IsList(oldHist.seq[lev_u]) then
            seq[lev_u] := updateTriple(oldHist.seq[lev_u],g,h);
          fi;
        fi; # if h has level less than lev_u nothing gets changed
      else 
        longer:=0; 
        if lev_v=lev_u and lev_v=level[g] and lev_u=level[h] then
          if not IsBound(oldHist.seq[lev_v]) then
            if g>h then seq[lev_v] := [1,IdWord,IdWord];
            elif g<h then seq[lev_v] := [-1,IdWord,IdWord];
            fi;
          elif IsList(oldHist.seq[lev_v]) then
            seq[lev_v] := updateTriple(oldHist.seq[lev_v],g,h);
          fi;
        else
          if lev_v=level[g] then
            if not IsBound(oldHist.seq[lev_v]) then
              seq[lev_v] := [0,monoidGenerators[g],IdWord];
            elif IsList(oldHist.seq[lev_v]) then
              seq[lev_v] := updateTriple(oldHist.seq[lev_v],g,0);
            fi;
          fi;
          if lev_u=level[h] then
            if not IsBound(oldHist.seq[lev_u]) then
              seq[lev_u] := [0,IdWord,monoidGenerators[h]];
            elif IsList(oldHist.seq[lev_u]) then
              seq[lev_u] := updateTriple(oldHist.seq[lev_u],0,h);
            fi;
          fi;
        fi;
      fi;

      InfoUpdateHistory("seq is now ",seq,"\n");
      if lev_v>lev_u then j := lev_v; else j := lev_u; fi;

      foundInt := false;
      outOfBounds := false;

      while j>= 1 do
        if IsBound(seq[j]) then
          if foundInt then Unbind(seq[j]);
          elif IsList(seq[j]) then
            if seq[j][1]=0 and Length(seq[j][2])=0 
                       and Length(seq[j][3])=0 then
              # if all entries are trivial delete that triple
              Unbind(seq[j]); 
            elif j<lev_v and j<lev_u then
              # only 1 or -1 should be stored, if anything
              InfoUpdateHistory("seq at ",j," to ",seq[j],"\n");
              InfoUpdateHistory("?1=",seq[j][2]," ",Length(seq[j][2])<> 0,"\n");
              InfoUpdateHistory("?2=",Length(seq[j][3])<> 0,"\n");
              InfoUpdateHistory("?3=",seq[j][1]<> 0,"\n");
              if Length(seq[j][2])<> 0 then seq[j] := 1;
              elif Length(seq[j][3])<> 0 then seq[j] := -1;
              elif seq[j][1]<>0 then seq[j] := seq[j][1];
              else Unbind(seq[j]);
              fi;
              InfoUpdateHistory("Set seq at ",j," to ",seq[j],"\n");
            elif j<lev_v or g=0 then
              if Length(seq[j][2])=0 and 
                  (seq[j][1]= -1 or Length(seq[j][3])<>0) then 
                seq[j] := -1;
                InfoUpdateHistory("Setting seq at ",j," to -1\n");
              fi;
            elif j<lev_u or h=0 then
              if Length(seq[j][3])=0 and 
                  (seq[j][1]= 1 or Length(seq[j][2])<>0) then 
                seq[j] := 1;
                InfoUpdateHistory("Setting seq at ",j," to 1\n");
              fi;
            fi;
            if IsList(N) 
               and IsBound(seq[j]) and IsList(seq[j]) 
                                # it WAS a list, but might not be any more
                  and Length(seq[j][3])>N[j] then
              outOfBounds := true;
            fi;
          fi;
          if IsBound(seq[j]) and IsInt(seq[j]) then foundInt := true; fi;
          if outOfBounds then j:= 0; fi;
        fi;
        j := j-1;
      od;

      InfoUpdateHistory("seq is now ",seq,"\n");
      InfoUpdateHistory("Leaving updateHistory\n");
      if outOfBounds then return [];
      else 
        hist := rec(longer := longer,lev_v := lev_v, lev_u := lev_u,
                 seq := seq);
        return [hist];
      fi;
    end;

    reductionHistory := function(history,g,h)
      local j,hh,newhist, seq;
# This function should probably be rewritten - it is presumably
# rather inefficient to call updateHistory

      InfoReductionHistory("Entering reductionHistory for ",
                                            history," ",g," ",h,"\n");
      if IsInt(h) then
        newhist := updateHistory(history,g,h,0); 
      else  # h is a word
        if g<>0 then Error("Arguments of reductionHistory out of range."); fi;
        j := 1;
        newhist := [StructuralCopy(history)];
        repeat
          hh := Position(generators,Subword(h,j,j));
          newhist := updateHistory(newhist[1],0,hh,0); 
          j := j+1;
        until j>Length(h) or Length(newhist)=0;
      fi;
           # newhist is a wrapped history or an empty list
      InfoReductionHistory("newhist is now ",newhist,"\n");
      if Length(newhist)=0 then return false;
      else 
        seq := newhist[1].seq;
        InfoReductionHistory("seq is now ",seq,"\n");
        j := maxLevel;
        while j>=1 do
          InfoReductionHistory("j= ",j," ",seq,"\n");
          if IsBound(seq[j]) then 
            if IsInt(seq[j]) then
              if seq[j]=1 then return true;
              else return false;
              fi;
            else # we have a list
              if Length(seq[j][2])<>0 then return true;
              elif Length(seq[j][3])<>0 then return false;
              elif seq[j][1]=1 then return true;
              else return false;
              fi;
            fi;
          fi;
          j := j-1;
        od;
      fi;
      Error("Reached end of reductionHistory function");
    end;

    betterThanHistory := function(hist1,hist2)
      local j;
      if hist1.longer=1 and hist2.longer=1 then

        if hist2.lev_v> hist2.lev_u then return false;
        elif hist2.lev_v = hist2.lev_u then
          j := hist2.lev_v;
          while not IsBound(hist2.seq[j]) do j := j-1; od;
          if IsInt(hist2.seq[j]) and hist2.seq[j]=1 
          then return false; 
          fi;
            # hist2 ALWAYS leads to a reduction so no history can be
            # better than it
        fi;

        if hist1.lev_v> hist1.lev_u then return true;
        elif hist1.lev_v = hist1.lev_u then
          j := hist1.lev_v;
          while not IsBound(hist1.seq[j]) do j := j-1; od;
          if IsInt(hist1.seq[j]) and hist1.seq[j]=1 
          then return false; 
          fi;
            # hist1 ALWAYS leads to a reduction
        fi;

      fi;
      return "dontknow";
    end;
        

  fi;

  if type = "shortlex" then 
    return rec(
    type := "shortlex",
      alphabet := generators,
      monoidGenerators := monoidGenerators,
      invAlphabet := invAlphabet,

      compareGens := function(g,h)
        if g=h then return 0; fi;
        # g and h should either both be integers or both be generators
        if IsWord(g) then
          g := Position(generators,g);
          h := Position(generators,h);
        fi;
        if g>h then return 1; else return -1; fi;
      end,
                     
      diffHistory := function(d,g,h)
        if h=0 then return rec(diff:=d,c0:=0,c1:=1);
        elif g>h then return rec(diff:=d,c0:=1,c1:=0);
        else return rec(diff:=d,c0:=-1,c1:=0); 
        fi; 
      end,

      updateDH := function(dh,dd,g,h,wd)
        if h>0 and dh.c0<>0 then return rec(diff:=dd,c0:=dh.c0,c1:=0);
        elif h=0 then return rec(diff:= dd,c0:= 0,c1:= 1);
        else Error("Parameters out of range for updateDH");
        fi;
      end,

      improveDH := function(dh1,dh2)
        if (dh2.c0=0 or (dh1.c0<>0 and dh1.c0>=dh2.c0))
          and (dh2.c1=0 or dh1.c1 >= dh2.c1)
            then return;
        else 
          if dh2.c0<>0 and (dh1.c0=0 or dh2.c0=1) then dh1.c0 := dh2.c0; fi;
          if dh2.c1=1 and dh1.c1=0 then dh1.c1 := dh2.c1; fi;
          return;
        fi;
      end,
 
      reductionDH := function(dh,g,h)
        if IsInt(h) then
          if h>0 and dh.c0=1 then return true;
          elif h=0 then return true; 
          fi;
        elif IsWord(h) then
          if g<>0 or Length(h)=0 or dh.c0=0  then
            Error("Parameters out of range for reductionDH");
          fi;
        fi;
        return false;
      end,
  
      emptyDH := function(dh)
        return dh.c0=0 and dh.c1=0;
      end,

      equalLengthsDH := function(dh)
         return dh.c0<>0;
      end,

      diffHistoryVtx := function(d,g,h)
        if g>0 then 
          if h=0 then return rec(diff:= d,gen := 0,back:= 0,len:= 1,lex := 0);
          elif g>h then return rec(diff:= d,gen := h,back:= 0,len:= 1,lex := 1);
          elif g<h then return rec(diff:= d,gen := h,back:= 0,len:= 1,lex := -1);
          else  Error("Parameters out of range for diffHistoryVtx");
          fi;
        else  Error("Parameters out of range for diffHistoryVtx");
        fi; 
      end,

      updateDHVtx := function(dhv,d,g,h)
        return rec(diff:=d,gen:=h,back:=dhv,len:=dhv.len+1,lex:=dhv.lex);
      end,

      reductionDHVtx := function(dhv,g,h)
        if IsInt(h) then
          if g>0 and (h=0 or dhv.lex=1) then return true; fi;
        elif IsWord(h) then
          if g<>0 or Length(h)=0  then
            Error("Parameters out of range for reductionDH");
          fi;
        fi;
        return false;
      end,

      betterThanDHVtx := function(dhv1,dhv2)
        # dhv1 and dhv2 are diffHistories for pairs (w,u) and (w,v)
        # which lead to the same word difference.
        # The function returns "false" if it is clear that 
        # whenever (wa,ub) leads to the identity word difference and 
        # wa > ub then also wa > vb and hence there is no value in
        # storing dhv1,
        # "true" if the above is not clear, BUT it is clear that
        # whenever (wa,vb) leads to the identity word difference and 
        # wa > vb then also wa > ub and hence we can store dhv1 instead
        # of dhv2,
        # "dontknow" if neither or the above is clear, and so we should
        # store both dhv1 and dhv2.
        
        # When dhv1 is better than dhv2,
        # we must have dhv1.diff=dhv2.diff and dhv1.gen and dhv2.gen
        # both non-zero.
        # We can only be certain that u<v if dhv1.lex=1 and dhv2.lex= -1,
        # since in that case we know that u<w and w<v

        local g1,g2;

        if dhv1.diff<> dhv2.diff then return "dontknow"; fi;

        g1:= dhv1.gen; g2 := dhv2.gen;
        if g1=0 and g2=0 then return false; # u and v are both shorter than w  
        elif g1=0 or g2=0 then return "dontknow";
        fi;

        if dhv1.lex=1 and dhv2.lex= -1 then return true;
        else return false;
        fi;

      end
    );
  elif type="wtlex" then
    return rec(
      type := "wtlex",
      alphabet := generators,
      monoidGenerators := monoidGenerators,
      invAlphabet := invAlphabet,
      weight := weight,
      getWeight := getWeight,

      compareGens := function(g,h)
        if g=h then return 0; fi;
        # g and h should either both be integers or both be generators
        if IsWord(g) then
          g := Position(generators,g);
          h := Position(generators,h);
        fi;
        if weight[g]>weight[h] then return 1;
        elif weight[g]<weight[h] then return -1;
        elif g>h then return 1; 
        else return -1; fi;
      end,
                     
      diffHistory := function(d,g,h)
        if h=0 then 
          return rec(diff:=d,c0:=0,w0:=0,c1 := 1,w1:= 1);
        elif g>h then 
          return rec(diff:=d,c0:=1,w0:=weight[g]-weight[h],c1:=0,w1:=0);
        elif g<h then 
          return rec(diff:=d,c0:= -1,w0:=weight[g]-weight[h],c1:=0,w1:=0);
        else Error("Parameters for diffHistory out of range"); 
        fi; 
      end,

      updateDH := function(dh,dd,g,h,wd)
        local c0,w0,c1,w1;
        if h>0 and dh.c0<>0 then 
          w0 := dh.w0 + weight[g] - weight[h];
          if w0 >= -getWeight(wd) then c0 := dh.c0; else c0 := 0; fi;
          return rec(diff:=dd,c0:=c0,w0 := w0,c1:=0,w1:=0);
        elif h=0 then 
          if dh.c0<>0 and dh.c1<>0 then
            # Choose the bigger weight difference in dh, add the weight of g 
            # to it and then set w1 to be the minimum of that and 1.
            # c1 is set to be dh.c0 if dh.w0>dh.w1, to be dh.c1 if dh.w1>dh.w0
            # and otherwise the larger of dh.c0 and dh.c1.
            if dh.w0>dh.w1 then
              if dh.w0+weight[g]>0 then w1 := 1; else w1 := dh.w0+weight[g]; fi;
              c1 := dh.c0;
            elif dh.w1>dh.w0 then
              if dh.w1+weight[g]>0 then w1 := 1; else w1 := dh.w1+weight[g]; fi;
              c1 := dh.c1;
            else
              if dh.w1+weight[g]>0 then w1 := 1; else w1 := dh.w1+weight[g]; fi;
              if dh.c1 >= dh.c0 then c1 := dh.c1; else c1 := dh.c0; fi;
            fi;
          elif dh.c0<>0 then
              if dh.w0+weight[g]>0 then w1 := 1; else w1 := dh.w0+weight[g]; fi;
              c1 := dh.c0;
          elif dh.c1<>0 then
            if dh.w1+weight[g]>0 then w1 := 1; else w1 := dh.w1+weight[g]; fi;
              c1 := dh.c1;
          fi;
          if w1 < - getWeight(wd) then c1 := 0; fi;
          return rec(diff:=dd,c0:=0,w0:=0,c1:=c1,w1:=w1);
        else
          Error("Parameters out of range for updateDH");
        fi;
      end,

      improveDH := function(dh1,dh2)
        if dh2.c0<>0 and 
            (dh1.c0=0 or dh1.w0<dh2.w0 or (dh1.w0=dh2.w0 and dh2.c0=1)) then
          dh1.c0 := dh2.c0; dh1.w0 := dh2.w0;
        fi;
        if dh2.c1<>0 and
            (dh1.c1=0 or dh1.w1 < dh2.w1 or (dh1.w1=dh2.w1 and dh2.c1=1)) then
          dh1.c1 := dh2.c1; dh1.w1 := dh2.w1;
        fi;
      end,
 
      reductionDH := function(dh,g,h)
        if IsInt(h) then
          if h>0 and dh.c0<>0 then
           # Return true if or some v,u with vg=_Gu, where l(vg)=l(u),
           # either wt(vg)>wt(u) or wt(vg)=wt(u) but vg>u lexicographically.
    
            if dh.w0 + weight[g]-weight[h]>0 or 
               (dh.w0+weight[g]-weight[h]=0 and dh.c0=1) then return true; fi;
          elif h=0 then
           # Return true if gfor some v,u with vg=_Gu, where l(vg)>l(u),
           # either wt(vg)>wt(u) or wt(vg)=wt(u) but vg>u lexicographically.
           # The cases l(v)=l(u) and l(v)>l(u) are considered separately
            if (dh.c0=1 and dh.w0 + weight[g]>=0) or
               (dh.c0= -1 and dh.w0 + weight[g]>0) or
               (dh.c1=1 and dh.w1 + weight[g]>=0) or
               (dh.c1= -1 and dh.w1 + weight[g]>0) then return true; fi;
          fi;
          return false;
        elif IsWord(h) then
          if g<>0 or Length(h)=0 or dh.c0=0  then
            Error("Parameters out of range for reductionDH");
          elif dh.w0 - getWeight(h) >0 or 
            ( dh.c0=1 and dh.w0-getWeight(h)=0) then return true;
          fi;
          return false;
        fi;
      end,
  
      emptyDH := function(dh)
        return dh.c0=0 and dh.c1=0;
      end,

      equalLengthsDH := function(dh)
         return dh.c0<>0;
      end,

      diffHistoryVtx := function(d,g,h)
        if g>0 then 
          if h=0 then return rec(diff:= d,gen := 0,back:= 0,
                         len:= 1,lex := 0,wtdiff:=weight[g]);
          elif g>h then return rec(diff:= d,gen := h,back:= 0,
                         len:= 1,lex := 1,wtdiff:=weight[g]-weight[h]);
          elif g<h then return rec(diff:= d,gen := h,back:= 0,
                         len:= 1,lex := -1,wtdiff:=weight[g]-weight[h]);
          else  Error("Parameters out of range for diffHistoryVtx");
          fi;
        else  Error("Parameters out of range for diffHistoryVtx");
        fi; 
      end,

      updateDHVtx := function(dhv,d,g,h)
        if g>0 then
          if h=0 then return rec(diff:=d,gen := h,back := dhv,
               len := dhv.len+1,lex := dhv.lex,wtdiff:=dhv.wtdiff+weight[g]);
          else return rec(diff:= d,gen := h,back:= dhv, len := dhv.len+1,
                      lex := dhv.lex,wtdiff:=dhv.wtdiff+weight[g]-weight[h]);
          fi;
        else  Error("Parameters out of range for updateDHVtx");
        fi; 
      end,

      reductionDHVtx := function(dhv,g,h)
        if IsInt(h) then
          if g>0 and h>0 then
            if dhv.wtdiff + weight[g]-weight[h]>0 or
              (dhv.wtdiff+weight[g]-weight[h]=0 and dhv.lex=1) then return true;
            fi;
          elif g>0 and h=0 then
            if dhv.wtdiff+weight[g]> 0 or
              (dhv.wtdiff+weight[g]=0 and dhv.lex=1) then return true; 
            fi;
          else  Error("Parameters out of range for reductionDHVtx");
          fi;
        elif IsWord(h) then
          if g<>0 or Length(h)=0  then
            Error("Parameters out of range for reductionDHVtx");
          elif dhv.wtdiff - getWeight(h) >0 or 
            ( dhv.wtdiff-getWeight(h)=0 and dhv.lex=1) then return true;
          fi;
        fi;
        return false;
      end,

      betterThanDHVtx := function(dhv1,dhv2)
        # dhv1 and dhv2 are diffHistories for pairs (w,u) and (w,v)
        # which lead to the same word difference.
        # The function returns "false" if it is clear that 
        # whenever (wa,ub) leads to the identity word difference and 
        # wa > ub then also wa > vb and hence there is no value in
        # storing dhv1,
        # "true" if the above is not clear, BUT it is clear that
        # whenever (wa,vb) leads to the identity word difference and 
        # wa > vb then also wa > ub and hence we can store dhv1 instead
        # of dhv2,
        # "dontknow" if neither or the above is clear, and so we should
        # store both dhv1 and dhv2.

        local g1,g2;

        if dhv1.diff<> dhv2.diff then return "dontknow"; fi;

        g1:= dhv1.gen; g2 := dhv2.gen;
        if g1=0 and g2=0 then 
          if dhv1.wtdiff>dhv2.wtdiff then return true;
          else return false; # u and v are both shorter than w  
          fi;
        elif g1=0 or g2=0 then return "dontknow";
        fi;

        if dhv1.wtdiff>dhv2.wtdiff or 
              (dhv1.wtdiff=dhv2.wtdiff and dhv1.lex=1 and dhv2.lex= -1)
                 then return true;
        else return false;
        fi;

      end

    );
  elif type = "wreathprod" then 
    return rec(
      type := "wreathprod",
      alphabet := generators,
      invAlphabet := invAlphabet,
      monoidGenerators := monoidGenerators,
      level := level,
      maxLevel := maxLevel,

      compareGens := function(g,h)
        if g=h then return 0; fi;
        # g and h should either both be integers or both be generators
        if IsWord(g) then
          g := Position(generators,g);
          h := Position(generators,h);
        fi;
        if level[g]>level[h] then return 1;
        elif level[g]<level[h] then return -1;
        elif g>h then return 1; 
        else return -1; fi;
      end,
                     

      diffHistory := function(d,g,h)
        return rec(diff:=d,histories:= [history(g,h)]);
      end,

      updateDH := function(dh,dd,g,h,wd)
        local new,N,i,j,histories;

        N := [];
        j := maxLevel;
        while j>0 do N[j] := 0; j := j-1; od;
        for i in [1..Length(wd)] do
          j:= level[Position(generators,Subword(wd,i,i))]; 
          N[j] := N[j]+1;
        od;
 
        histories := [];
        for i in [1..Length(dh.histories)] do
          Append(histories,updateHistory(dh.histories[i],g,h,N));
        od;
        histories := Set(histories);
        return rec(diff := dd,histories := histories);
      end,


      improveDH := function(dh1,dh2)
        Append(dh1.histories,dh2.histories);
        dh1.histories := Set(dh1.histories);
      end,
 
      reductionDH := function(dh,g,h)
        local histories,hist,seq,i,j,hh;
        histories := dh.histories;
        InfoReductionDH("Entering reductionDH with ",dh," ",g," ",h,"\n");

        for i in [1..Length(histories)] do
          InfoReductionDH("i:=",i," ",histories[i],"\n");
          if reductionHistory(histories[i],g,h) then return true; fi;
        od;
        return false;
      end,
  
      emptyDH := function(dh)
        return Length(dh.histories)=0;
      end,

      equalLengthsDH := function(dh)
        local i;
        for i in [1..Length(dh.histories)] do
          if dh.histories[i].longer=0 then return true; fi;
        od;
        return false;
      end,

      diffHistoryVtx := function(d,g,h)
        InfoDiffHistoryVtx("New diffHistoryVtx ",g," ",h," ",history(g,h),"\n");
        if g>0 then 
          return rec(diff:=d,gen := h,back:=0,len := 1,history:=history(g,h));
        elif g=h then  Error("g=h, Parameters out of range for diffHistoryVtx");
        else  Error("Parameters out of range for diffHistoryVtx");
        fi; 
      end,

      updateDHVtx := function(dhv,d,g,h)
        local newHist;
        newHist := updateHistory(dhv.history,g,h,0);
        InfoDiffHistoryVtx("Updates diffHistoryVtx ",g," ",h," ",newHist,"\n");
        if Length(newHist)=1 then
          return rec(diff:=d,gen:=h,back:=dhv,len:=dhv.len+1,
                                            history:=newHist[1]);
        else
          Error("Parameters out of range for diffHistoryVtx");
        fi;
      end,

      reductionDHVtx := function(dhv,g,h)
        return reductionHistory(dhv.history,g,h);
      end,

      betterThanDHVtx := function(dhv1,dhv2)
        # dhv1 and dhv2 are diffHistories for pairs (w,u) and (w,v)
        # which lead to the same word difference.
        # The function returns "false" if it is clear that 
        # whenever (wa,ub) leads to the identity word difference and 
        # wa > ub then also wa > vb and hence there is no value in
        # storing dhv1,
        # "true" if the above is not clear, BUT it is clear that
        # whenever (wa,vb) leads to the identity word difference and 
        # wa > vb then also wa > ub and hence we can store dhv1 instead
        # of dhv2,
        # "dontknow" if neither or the above is clear, and so we should
        # store both dhv1 and dhv2.
        
        if dhv1.diff <> dhv2.diff then return "dontknow"; 
        elif dhv1.history=dhv2.history then return false;
        else return betterThanHistory(dhv1.history,dhv2.history);
        fi;
      end
    );
  else
    Error("Cannot construct word order of type ",type,"\n");
  fi; 
end;

DiffInverseList := function(D)

  local diffInverse, # list of inverses
        count, # integer loop parameter
        numSymbols, # number of alphabet symbols
        g,h, # indexes for alphabet symbols
        d, d_inv, dd, dd_inv; # states of D

  if IsBound(D.diffInverse) then return D.diffInverse; fi;

  BFSFSA(D); 
  numSymbols := D.alphabet.base.size;
  diffInverse := 0*[1..D.states.size];
  diffInverse[1] := 1;
  count := 1;
  d := 1; d_inv := 1;
  repeat
    for g in [1..numSymbols+1] do
      for h in [1..numSymbols+1] do
        if g<>numSymbols+1 or h<>numSymbols+1 then
          dd:= TargetDFA(D,[g,h],d);
          dd_inv:= TargetDFA(D,[h,g],d_inv);
          if (dd<>0 and dd_inv=0) or (dd=0 and dd_inv<>0) then
            Error ("DiffInverseList: d=",d," dd=",dd," g=",g," h=",
                           h,"\nd_inv=",d_inv,"dd_inv=",dd_inv,"\n");
          fi;
          if dd<> 0 and diffInverse[dd]=0 then 
            diffInverse[dd] := dd_inv; count := count+1; fi;
          if dd_inv<>0 and diffInverse[dd_inv]=0 then 
            diffInverse[dd_inv] := dd; count := count+1; fi;
        fi;
      od;
    od;
    d := d+1;
    d_inv := diffInverse[d];
  until count = D.states.size;
  
  D.diffInverse := diffInverse;
  return diffInverse;

end;

WdAcceptor := function(D,order)
  local WA, numSymbols, stateList,
  s,sg,t, # states of W
  S,Sg, # sets of difference histories corresponding to s and sg
  g,h,dollar,
  d,dd,d0, # states of D
  diffInverse, count,
  dh,ddh,stored, # difference histories
  fails, brk, i;

  WA := FSA(D.alphabet.base);
  numSymbols := WA.alphabet.size;
  d0 := D.initial[1];
  dollar := numSymbols+1;

  diffInverse := DiffInverseList(D);
  
  stateList := [[]]; 
  # stateList[i] is the set of difference histories corresponding to state i -
  # the start state corresponds to the empty set

  # first we define targets for the start state
  s:= 1;
  for g in [1..numSymbols] do
    Sg :=[];
    fails := false;
  # first check to see if g is equal to the identity
    dd :=  TargetDFA(D,[g,dollar],d0);
    if dd=d0 then fails := true;
    elif dd>0 then
      AddSet(Sg, order.diffHistory(dd,g,0));
    fi;
    # now check to see if g is equal to another generator
    h:=1;
    while not fails and  h <= numSymbols do
      dd :=  TargetDFA(D,[g,h],d0);
      if dd=d0 then if order.compareGens(g,h)=1 then fails := true; fi; 
      elif dd>0 then
        ddh := order.diffHistory(dd,g,h);
        if order.reductionDH(ddh,0,D.states.names[diffInverse[dd]]) then
          fails := true;
        fi;
      # Run through Sg to see if there's already a diff history for dd
      # in there. If so, remove it and modify ddh to include its info.
        if not fails then
          brk := false;
          for stored in Sg do
            if not brk and  stored.diff = ddh.diff then
              RemoveSet(Sg,stored);
              order.improveDH(ddh,stored);
              brk:=true;
            fi;
          od;
          AddSet(Sg,ddh); 
        fi;
      fi;
      h := h+1;
    od; # end of loop for h
    if not fails then 
      # we look to see if there's an existing state corresponding to
      # the set Sg of difference histories
      sg:= 0;
      brk := false;
      for i in [2..WA.states.size] do
        if not brk and stateList[i]=Sg then
          sg:= i;
          brk:= true; 
        fi;
      od;
      if sg=0 then
      # we need to build a new state to be the target of s under g
        Add(stateList,Sg);
        AddStateFSA(WA);
        sg := WA.states.size;
        SetAcceptingFSA(WA,sg,true);
      fi;
      AddEdgeFSA(WA,g,s,sg);
    fi;
  od;
       
  # Now we define targets for all states after the start state,
  # until every state has all its targets defined.
 
  s := 2;

  while s <= WA.states.size do
    S := stateList[s];
    if s mod 100 = 0 then
      InfoWdAcceptor("Computing images of ",s,"-th state out of ",WA.states.size,"\n");
    fi;
    for g in [1..numSymbols] do
      t := TargetDFA(WA,g,WA.initial[1]);
      if t=0 then fails := true; 
      else 
        Sg := StructuralCopy(stateList[t]);
        fails := false;
        i := 1;
        while not fails and i <= Length(S) do
          dh := S[i];
          d := dh.diff;
          dd := TargetDFA(D,[g,dollar],d);
          if dd=d0 then 
            if order.reductionDH(dh,g,0) then fails := true; fi;
          elif dd>0 then
            ddh := order.updateDH(dh,dd,g,0,D.states.names[dd]);
            if not order.emptyDH(ddh) then 
              brk := false;
              for stored in Sg do
                if not brk and stored.diff=ddh.diff then
                  RemoveSet(Sg,stored);
                  order.improveDH(ddh,stored);
                  brk := true;
                fi;
              od;
              AddSet(Sg,ddh);
            fi;
          fi;
          if order.equalLengthsDH(dh) then
            h := 1;
            while not fails and h <= numSymbols do
              dd := TargetDFA(D,[g,h],d);
              if dd=d0 then
                if order.reductionDH(dh,g,h) then fails := true; fi;
              elif dd>0 then
                 ddh := order.updateDH
                                  (dh,dd,g,h,D.states.names[dd]);
                if not order.emptyDH(ddh) then 
                  if order.reductionDH
                         (ddh,0,D.states.names[diffInverse[dd]]) then
                    fails := true;
                  else
                    brk := false;
                    for stored in Sg do
                      if not brk and  stored.diff=ddh.diff then
                        RemoveSet(Sg,stored);
                        order.improveDH(ddh,stored);
                        brk := true;
                      fi;
                    od;
                    AddSet(Sg,ddh);
                  fi;
                fi;
              fi;
              h := h+1;
            od; # end of loop for h
          fi;
          i := i+1;
        od; # end of loop over S
      fi;
      
      if not fails then
        sg := 0;
        for i in [2..WA.states.size] do
          if sg=0 and stateList[i]=Sg then sg:= i; fi;
        od;
        if sg=0 then
          Add(stateList,Sg);
          AddStateFSA(WA);
          sg := WA.states.size;
          SetAcceptingFSA(WA,sg,true);
        fi;
        AddEdgeFSA(WA,g,s,sg);
      fi;
    od;  # end of loop for g
    s := s+1;
  od; # end of loop for s
 
  return WA;


          
end;

        

DiffReducedWord := function(D,order,w)

## this function is a generalisation of the rewrite function used
## in Derek Holt's KBmag Package for the shortlex order.
## We read through the word v which is to be reduced, one generator at
## a time. 
## Let x be the generator in position posn.
## Where a is any prefix of the word v finishing before that position,
## all word differences equal to a^-1b  where u is no longer than
## w have been found, and form the vertices of a tree.
## Let dhv be one such vertex. At dhv is stored
## 1) the corresponding state of the word difference machine, d
## 2) the length of the word w, the maximal suffix of  a such
## that d = w^-1u (for a suffix w of a)
## 3) an integer labelling the last generator y of u, if u has the
## same length as w, otherwise 0 - the integer is h where column
## h of the difference machine represents transitions on y
## 4) a pointer to the a `previous' vertex corresponding to the
## word difference w'^-1u', where w' is the max. prefix of w
## and u' is the max prefix of u if u has the same length as w,
## but otherwise is equal to u. Additional information
## varies according to the word order and indicates the
## relationship between w and u in the order. 
  
  local doneSub, # boolean variables, initially false,
     # set true after a reduction, but doneSub is reset to false in each loop  
  Len, len, redlen,i,j,
  posn, # current position in word (range from 1 to  Length(w))
  vno, # the position on the queue of the vertex currently being processed
  d,d0,dd,dD, # states of D
  x,y, # generators
  xx,yy, # integers indexing the generators x and y
  ww, # word, 
  dhv, ddhv, # vertices of the tree
  lastvno, # the position of the last vertex on the queue
  firstvno, # the position of the first vertex on the queue in the current
           # layer (if there is one)
  dhvList, # queue of vertices
  LastDhv, # LastDhv[i] is the position of the last vertex on the queue 
           # at the end of layer i.
  diffInverse,
  seen, # boolean list of differences seen so far
  numSymbols,dollar,
  bugw1, bugw2,
  StoreBetterDHVtx,
  IdWord;

  IdWord:=w^0;
  

  StoreBetterDHVtx := function(dhv,d)
    ## dhv is a vertex with difference d.
    ## dhvList is known to contain a vertex with difference d
    ## in the layer from firstvno and lastvno.
    ## We check through the list, and only add dhv to the list if we cannot
    ## prove that the reduction info it carries isn't already carried by
    ## a vertex already on the list. As we add dhv, it may be possible to
    ## remove other vertices from the list.
    local i,j,
          bT; # true, false or "dontknow", result of comparing two vertices 
              # corresponding to the same difference

    i := firstvno-1;
    j:= 0;
    bT := "dontknow";
    InfoStoreBetterDHVtx("In StoreBetterDHVtx ",lastvno," ");
    while j<>fail and bT<>false do
      # We search through all the vertices defined at this layer, and
      # compare dh with each vertex associated with the difference d 
      j:= PositionProperty(dhvList{[i+1..lastvno]},x->x.diff=d);
      # j is the index of a vertex within the sublist
      # of vertices at this layer, rather than the index within the whole list.
      if j<>fail then
        i := i+j; 
            # i is reset to be index of the vertex in the full list
        bT := order.betterThanDHVtx(dhv,dhvList[i]);

        # If bT is false then dhvList[i] is at least as good as dh,
        # so there's no point in adding dh to the list.
        # If bT is true then dh is better than dhvList[i],
        # so dhvList[i] can be deleted from the list.
        # if bT is "dontknow" it's not clear which is better.

        if bT=true then 
          InfoStoreBetterDHVtx("Deleting ",dhvList[i],"\n");
          dhvList := dhvList{Concatenation([1..i-1],[i+1..lastvno])}; 
          lastvno := lastvno-1;
        fi;
      fi;
    od;
    if bT<>false then 
      Add(dhvList,dhv); lastvno := lastvno+1; 
      InfoStoreBetterDHVtx("Adding ",dhvList[lastvno],"\n");
    fi;
    InfoStoreBetterDHVtx(lastvno,"\n");
  end;

  diffInverse := DiffInverseList(D);
  numSymbols := D.alphabet.base.size;
  dollar := numSymbols+1;

  dhvList := [];
  LastDhv := [];


  d0 := 1;
  posn := 1;
  firstvno := 1;
  lastvno := 0;

  InfoDiffReducedWord("DiffReducedWord called for ",w,"\n");
  while posn <= Length(w) do
    Len := Length(w);
    InfoDiffReducedWord("Word ",w," posn ",posn,"\n");
    doneSub := false;
    seen := BlistList([1..D.states.size],[]);
    x := Subword(w,posn,posn);
    xx := Position(order.alphabet,x);

# First we look for reductions of x itself, and if there are
# none construct a vertex for each x^-1y, y a generator or identity
# which is a non-trivial word difference.

    d := d0;
    dhv := 0;
    len := 0;

    dd :=  TargetDFA(D,[xx,dollar],d);

    if dd=d0 then
      # x reduces to the identity, so we reduce w
      InfoDiffReducedWord2("Word ",w," posn ",posn,"->id\n");
      w := SubstitutedWord(w,posn,posn,IdWord);
      doneSub := true;
# SubstitutedWord may do free reduction - if it does we have to backtrack.
# We subtract (Len-1-Length(w))/2 from posn to deal with this.
# In fact this might take us back too far, if some of the free reduction
# is with the later rather than the earlier section of the word.
      posn := posn - (Len-1-Length(w))/2;
      if posn<1 then posn := 1; fi; 
    elif dd<>0 then
      ddhv := order.diffHistoryVtx (dd,xx,0); 
      if seen[dd]=true then
        StoreBetterDHVtx(ddhv,dd);
      else Add(dhvList,ddhv); lastvno := lastvno+1; seen[dd] := true;
      fi;
    fi;

    yy := 1;
    while not doneSub and yy <= numSymbols do 
      y := order.alphabet[yy];
      dd := TargetDFA(D,[xx,yy],d0);
      if dd=d0 then 
        if order.compareGens(xx,yy)=1 then
          # x reduces to y, so we reduce w
          InfoDiffReducedWord2("Word ",w," posn ",posn,"->",y,"\n");
          w := SubstitutedWord(w,posn,posn,y);
          doneSub := true;
# SubstitutedWord may do free reduction - if it does we have to backtrack.
# We subtract (Len-Length(w))/2 from posn to deal with this.
# In fact this might take us back too far, if some of the free reduction
# is with the later rather than the earlier section of the word.
          posn := posn - (Len - Length(w))/2;
          if posn<1 then posn := 1; fi; 
        fi;
      elif dd<>0 then
        ddhv := order.diffHistoryVtx(dd,xx,yy);
        if order.reductionDHVtx
                 (ddhv,0,D.states.names[diffInverse[dd]]) then
        # x reduces to y*dd_inv, where dd_inv is the word difference 
        # inverse to dd
          InfoDiffReducedWord2("Word ",w," posn ",posn,"->",
                          y*D.states.names[diffInverse[dd]],"\n");
          w := SubstitutedWord(w,posn,posn,y*D.states.names[diffInverse[dd]]);
          doneSub := true;
# SubstitutedWord may do free reduction - if it does we have to backtrack.
# We subtract (Len+Length(D.states.names[diffInverse[dd]]-Length(w))/2 
# from posn to deal with this.
# In fact this might take us back too far, if some of the free reduction
# is with the later rather than the earlier section of the word.
          posn := posn -(Len + Length(D.states.names[diffInverse[dd]])
                  -Length(w))/2;
          if posn<1 then posn := 1; fi; 
InfoDiffReducedWord2("Reduction type 1\n");
        else
          if seen[dd]=true then
            StoreBetterDHVtx(ddhv,dd);
          else Add(dhvList,ddhv); lastvno := lastvno+1; seen[dd] := true;
          fi;
        fi;
      fi; 

      yy := yy+1;

    od; # end of loop over yy
       
    # Now we work through the vertices created at the last round (i.e.
    # those corresponding to non-trivial suffices of the prefix
    # a of v which was read before x) and see if one of these
    # points to a reduction of ax. If not we create the next
    # layer of vertices.

    if not doneSub and posn>1 then
      if posn=2 then vno:=1;
      else vno := LastDhv[posn-2]+1;
        # the position on the list of the first of the vertices
        # created in the last round
      fi;
      while not doneSub and vno <= LastDhv[posn-1] do
        InfoDiffReducedWord2("vno ",vno,"\n");
        dhv := dhvList[vno];
        len := dhv.len;
        d := dhv.diff;
        dd := TargetDFA(D,[xx,dollar],d);
        if dd=d0 then
          if order.reductionDHVtx(dhv,xx,0) then
            ww := IdWord;
            ddhv := dhv;
            while ddhv<>0 and ddhv.gen=0 do ddhv := ddhv.back; od;
            while ddhv<>0 do 
              ww := order.alphabet[ddhv.gen] * ww; ddhv := ddhv.back; 
            od;
InfoDiffReducedWord2("Reduction type 2\n");
            InfoDiffReducedWord2("Word ",w," posns",posn-len,"-",posn,
                        "->",ww,"\n");
            w := SubstitutedWord(w,posn-len,posn,ww);
            doneSub := true;
# SubstitutedWord may do free reduction - if it does we have to backtrack
# further than we would need to otherwise.
# We subtract (Len+Length(ww)-len-1-Length(w))/2 from posn 
# to deal with this.
# In fact this might take us back too far, if some of the free reduction
# is with the later rather than the earlier section of the word.
            posn := posn -len -(Len+Length(ww)-len--Length(w))/2;
            if posn<1 then posn := 1; fi; 
          fi;
        elif dd<> 0 then
          ddhv := order.updateDHVtx (dhv,dd,xx,0);
 
          if seen[dd]=true then
            StoreBetterDHVtx(ddhv,dd);
          else Add(dhvList,ddhv); lastvno := lastvno+1; seen[dd] := true;
          fi;
        fi;

        if dhv.gen<>0 then
          yy := 1;
          while not doneSub and yy <= numSymbols do 
            y := order.alphabet[yy];
            dd := TargetDFA(D,[xx,yy],d);
            if dd=d0 then
              if order.reductionDHVtx(dhv,xx,yy) then
                ww := y;
                ddhv := dhv;
                while ddhv<>0 do 
                  ww := order.alphabet[ddhv.gen] * ww; ddhv := ddhv.back; 
                od;
InfoDiffReducedWord2("Reduction type 3 posn ",posn," len ",len,"\n");
InfoDiffReducedWord2(w," reduced using ",ww," to give ");
                w := SubstitutedWord(w,posn-len,posn,ww);
InfoDiffReducedWord2(w,"\n");
                doneSub := true;
# SubstitutedWord may do free reduction - if it does we have to backtrack
# further than we would need to otherwise.
# We subtract (Len+Length(ww)-len-1-Length(w))/2 from posn 
# to deal with this.
# In fact this might take us back too far, if some of the free reduction
# is with the later rather than the earlier section of the word.
                posn := posn -len -(Len+Length(ww)-len-1-Length(w))/2;
                if posn<1 then posn := 1; fi; 
              fi;
            elif dd<>0 then
              ddhv := order.updateDHVtx(dhv,dd,xx,yy);
              if order.reductionDHVtx
                   (ddhv,0,D.states.names[diffInverse[dd]]) then
              # for some suffix a of the word read so far, 
              # some b of the same length as a,
              # ax reduces to by*dd_inv, where dd_inv is the word difference
              # inverse to dd
InfoDiffReducedWord2("Reduction type 4\n");
            InfoDiffReducedWord2("xx ",xx," yy ",yy," dhv ",dhv,"\n");
            InfoDiffReducedWord2("x ",x," y ",y," inv_diff ",
                              D.states.names[diffInverse[dd]],"\n");
                ww := y*D.states.names[diffInverse[dd]];
InfoDiffReducedWord2("ww ",ww,"\n");
                ddhv := dhv;
                while ddhv<>0 do 
                  ww := order.alphabet[ddhv.gen] * ww; ddhv := ddhv.back; 
                od;
InfoDiffReducedWord2("ww ",ww,"\n");
            InfoDiffReducedWord2("Word ",w," posns",posn-len,"-",posn,
                        "->",ww,"\n");
                bugw1 := w;
                w := SubstitutedWord(w,posn-len,posn,ww);
                bugw2 := w;
                if bugw1=bugw2 then Error("Word hasn't changed."); fi;
                doneSub := true;
# SubstitutedWord may do free reduction - if it does we have to backtrack
# further than we would need to otherwise.
# We subtract (Len+Length(ww)-len-1-Length(w))/2 from posn 
# to deal with this.
# In fact this might take us back too far, if some of the free reduction
# is with the later rather than the earlier section of the word.
                posn := posn -len -(Len+Length(ww)-len-1-Length(w))/2;
                if posn<1 then posn := 1; fi; 
              else
                if seen[dd]=true then
                  StoreBetterDHVtx(ddhv,dd);
                else 
                  Add(dhvList,ddhv); lastvno := lastvno+1; seen[dd] := true;
                fi;
              fi;
            fi;
            yy := yy+1;
          od; # end of loop over yy
        fi;
        vno := vno + 1;
      od; # end of loop over vno
    fi; 

    if doneSub then
      if posn=1 then 
        dhvList := []; firstvno := 1; lastvno := 0;
      else 
        dhvList := dhvList{[1..LastDhv[posn-1]]};
        firstvno := LastDhv[posn-1]+1; lastvno := LastDhv[posn-1];
      fi;
    else 
      LastDhv[posn] := Length(dhvList); 
      firstvno := LastDhv[posn]+1; lastvno := LastDhv[posn];
      posn := posn + 1;
    fi;
  od;     

  InfoDiffReducedWord("Reduction is ",w,"\n");
  return w;
end;

SubstringClosure := function(D,order,inverses)
# inverses could be true or false

  local DC,s,s_inv,t,t_inv, # states
        a,b,a_inv,a_inv_index,b_inv_index,
        numSymbols,
        oldNumStates,
        dollar,
        len,
        w,w_inv,ww,
        diffInverse;

  
  DC := StructuralCopy(D);
  if (inverses) then
    diffInverse := DiffInverseList(DC);
  fi;
  numSymbols := D.alphabet.base.size;
  dollar := numSymbols +1;

  s:= 1;
  while s<=DC.states.size do
   InfoSubstringClosure("s:=",s,"Total number of states:=",DC.states.size,"\n");
    oldNumStates := DC.states.size;
    w :=  DC.states.names[s];
    if inverses then
      s_inv := diffInverse[s];
      w_inv :=  DC.states.names[s_inv];
    fi;
    len := Length(w);
    if len>=2 then
      a := Subword(w,1,1);
      b := Subword(w,len,len);
      a_inv_index :=order.invAlphabet[Position(order.alphabet,a)];
      b_inv_index :=order.invAlphabet[Position(order.alphabet,b)];
      a_inv := order.alphabet[a_inv_index];

      if TargetDFA(DC,[dollar,b_inv_index],s)=0 then
        ww := Subword(w,1,len-1);
        t := Position(DC.states.names,ww);
        if t=fail then 
          AddStateFSA(DC,ww);
          t := DC.states.size;
        fi;
        AddEdgeFSA(DC,[dollar,b_inv_index],s,t);
# the above edge is labelled with (dollar,b^-1)
        AddEdgeFSA(DC,[dollar,Position(order.alphabet,b)],t,s);
      fi;

      if inverses and TargetDFA(DC,[b_inv_index,dollar],s_inv)=0 then
        ww := DiffReducedWord(D,order,b*w_inv);
        t_inv := Position(DC.states.names,ww);
        if t_inv=fail and IsBound(diffInverse[t]) then
          Error("t_inv problem 1 ",t," ",diffInverse[t],"\n"); fi;
        if t_inv=fail then 
          AddStateFSA(DC,ww);
          t_inv := DC.states.size;
        fi;
        AddEdgeFSA(DC,[b_inv_index,dollar],s_inv,t_inv);
        AddEdgeFSA(DC,[Position(order.alphabet,b),dollar],t_inv,s_inv);
        diffInverse[t] := t_inv;
        diffInverse[t_inv] := t;
        InfoSubstringClosure("Set ",t," and ",t_inv," to be inverse pairs.\n");
      fi;

      if TargetDFA(DC,[Position(order.alphabet,a),dollar],s)=0 then
        ww := Subword(w,2,len);
        t := Position(DC.states.names,ww);
        if t=fail then 
          AddStateFSA(DC,ww);
          t := DC.states.size;
        fi;
        AddEdgeFSA(DC,[Position(order.alphabet,a),dollar],s,t);    
        AddEdgeFSA(DC,
          [a_inv_index,dollar],t,s);
      fi;

      if inverses and 
          TargetDFA(DC,[dollar,Position(order.alphabet,a)],s_inv)=0 then
        ww := DiffReducedWord(D,order,w_inv*a);
        t_inv := Position(DC.states.names,ww);
        if t_inv=fail and IsBound(diffInverse[t]) then
          Error("t_inv problem 2\n"); fi;
        if t_inv=fail then 
          AddStateFSA(DC,ww);
          t_inv := DC.states.size;
        fi;
        AddEdgeFSA(DC,[dollar,Position(order.alphabet,a)],s_inv,t_inv);    
        AddEdgeFSA(DC,[dollar,a_inv_index],t_inv,s_inv);
        diffInverse[t] := t_inv;
        diffInverse[t_inv] := t;
        InfoSubstringClosure("Set ",t," and ",t_inv," to be inverse pairs.\n");
      fi;
    fi;
    s := s+1;
  od;
  return DC;
end;

CorrectDiffMachine := function(R,order)

  local pair, w1,w2,g,newD, inverses,
    change,
    dollar, d,d_inv,dd,dd_inv,wd,wd_inv,len1,len2,len,i,
    x,x_inv,xx,y,y_inv,yy,
    IdWord;
  
  InfoCorrectDiffMachine("R.wg:=",R!.wg,"\n");
  newD := StructuralCopy(R!.diff2);
  inverses := DiffInverseList(newD);
  dollar := R!.diff2.alphabet.base.size+1;
  IdWord := R!.wg[1][1]^0;
  for pair in R!.wg do
    InfoCorrectDiffMachine("pair",pair,"\n");
    change := false;   
    w1 := pair[1];
    g := pair[2];
    w2 := DiffReducedWord(R!.diff2,order,w1*g);
    InfoCorrectDiffMachine2("w1 ",w1," g ",g," w2 ",w2,"\n");
    d := 1; d_inv := 1;
    len1 := Length(w1);
    len2 := Length(w2);
    if len2>len1 then len := len2; else len := len1; fi;
    i := 1;
    while i<= len do
      InfoCorrectDiffMachine2("i ",i,"\n");
      if i<=len1 then
        x := Subword(w1,i,i);
        xx := Position(order.alphabet,x);
        x_inv := order.alphabet[order.invAlphabet[xx]];
      else
        x := IdWord;
        xx := dollar;
        x_inv := IdWord;
      fi;
      if i<=len2 then
        y := Subword(w2,i,i);
        yy := Position(order.alphabet,y);
        y_inv := order.alphabet[order.invAlphabet[yy]];
      else
        y := IdWord;
        yy := dollar;
        y_inv := IdWord;
      fi;
      dd := TargetDFA(newD,[xx,yy],d);
      if i=len then
        wd := DiffReducedWord(R!.diff2,order,g);
        if dd<>0 and newD.states.names[dd] <> wd then
          DeleteEdgeFSA(newD,[xx,yy],d,dd); 
          InfoCorrectDiffMachine("Replacing edge to ",newD.states.names[dd],
                       " by edge to ",wd,"\n");
          dd:= 0;
        fi;
        if dd=0 then
          change:= true;
          dd := Position(newD.states.names,wd);
          if dd <> fail then AddEdgeFSA(newD,[xx,yy],d,dd); fi;
        fi;
      elif dd=0 then
        change:= true;
        wd := DiffReducedWord(R!.diff2,order,x_inv*newD.states.names[d]*y);
        dd := Position(newD.states.names,wd);
        if dd <> fail then AddEdgeFSA(newD,[xx,yy],d,dd); fi;
      else wd := newD.states.names[dd];
      fi;
      dd_inv := TargetDFA(newD,[yy,xx],d_inv);
      if i=len then
        wd_inv := DiffReducedWord(R!.diff2,order,
                R!.alphabet[R!.invAlphabet[Position(R!.alphabet,g)]]);
        if dd_inv<>0 and newD.states.names[dd_inv] <> wd_inv then
          DeleteEdgeFSA(newD,[yy,xx],d_inv,dd_inv); 
          InfoCorrectDiffMachine("Replacing edge to ",
            newD.states.names[dd_inv]," by edge to ",wd_inv,"\n");
          dd_inv:= 0;
        fi;
        if dd_inv=0 then
          change:= true;
          dd_inv := Position(newD.states.names,wd_inv);
          if dd_inv <> fail then AddEdgeFSA(newD,[yy,xx],d_inv,dd_inv); fi;
        fi;
      elif dd_inv=0 then
        change := true;
        wd_inv :=
           DiffReducedWord(R!.diff2,order,y_inv*newD.states.names[d_inv]*x);
        dd_inv := Position(newD.states.names,wd_inv);
        if dd_inv <> fail then AddEdgeFSA(newD,[yy,xx],d_inv,dd_inv); fi;
      else wd_inv := newD.states.names[dd_inv];
      fi;
      if dd=fail and dd_inv=fail then
        AddStateFSA(newD,wd);
        dd := newD.states.size;
        InfoCorrectDiffMachine2(
                         "Creating new state numbered ",dd," for ",wd,"\n");
        AddEdgeFSA(newD,[xx,yy],d,dd);
        if wd=wd_inv then
          dd_inv := dd;
          AddEdgeFSA(newD,[yy,xx],d_inv,dd_inv);
          inverses[dd] := dd;
        else
          AddStateFSA(newD,wd_inv);
          dd_inv := newD.states.size;
          InfoCorrectDiffMachine2(
               "Creating new state numbered ",dd_inv," for ",wd_inv,"\n");
          AddEdgeFSA(newD,[yy,xx],d_inv,dd_inv);
          inverses[dd] := dd_inv;
          inverses[dd_inv] := dd;
        fi;
      elif dd_inv=fail then
        dd_inv := inverses[dd];
        AddEdgeFSA(newD,[yy,xx],d_inv,dd_inv); 
      elif dd=fail then
        dd := inverses[dd_inv];
        AddEdgeFSA(newD,[xx,yy],d,dd);
      fi;
      InfoCorrectDiffMachine2("dd ",dd," wd ",wd,"\n");
      InfoCorrectDiffMachine2("dd_inv ",dd_inv," wd_inv ",wd_inv,"\n");
      d := dd;
      d_inv := dd_inv;
      i := i+1;
    od;
    if change=false then
      InfoCorrectDiffMachine(
                 "No changes made to difference machine for ",pair,"\n");
    fi;
  od;
  R!.diff2 := newD;
end;

CorrectDiffMachineFromTriples := function(R,order)

  local triple, w1,w2,g,newD, inverses,
    change,
    dollar, d,d_inv,dd,dd_inv,wd,wd_inv,len1,len2,len,i,
    x,x_inv,xx,y,y_inv,yy,
    IdWord;
  
  InfoCorrectDiffMachine("R.wgw:=",R!.wgw,"\n");
  newD := StructuralCopy(R!.diff2);
  inverses := DiffInverseList(newD);
  dollar := R!.diff2.alphabet.base.size+1;
  InfoCorrectDiffMachine2("At top of loop over triples\n");
  IdWord := R!.wgw[1]^0;
  for triple in R!.wgw do
    InfoCorrectDiffMachine("triple",triple,"\n");
    change := false;   
    w1 := triple[1];
    g := triple[2];
    w2 := triple[3];
    d := 1; d_inv := 1;
    len1 := Length(w1);
    len2 := Length(w2);
    if len2>len1 then len := len2; else len := len1; fi;
    i := 1;
    while i<= len do
      InfoCorrectDiffMachine2("i ",i,"\n");
      if i<=len1 then
        x := Subword(w1,i,i);
        xx := Position(order.alphabet,x);
        x_inv := order.alphabet[order.invAlphabet[xx]];
      else
        x := IdWord;
        xx := dollar;
        x_inv := IdWord;
      fi;
      if i<=len2 then
        y := Subword(w2,i,i);
        yy := Position(order.alphabet,y);
        y_inv := order.alphabet[order.invAlphabet[yy]];
      else
        y := IdWord;
        yy := dollar;
        y_inv := IdWord;
      fi;
      dd := TargetDFA(newD,[xx,yy],d);
      if i=len then
        wd := DiffReducedWord(R!.diff2,order,g);
        if dd<>0 and newD.states.names[dd] <> wd then
          DeleteEdgeFSA(newD,[xx,yy],d,dd); 
          InfoCorrectDiffMachine("Replacing edge to ",newD.states.names[dd],
                       " by edge to ",wd,"\n");
          dd:= 0;
        fi;
        if dd=0 then
          change:= true;
          dd := Position(newD.states.names,wd);
          if dd <> fail then AddEdgeFSA(newD,[xx,yy],d,dd); fi;
        fi;
      elif dd=0 then
        change:= true;
        wd := DiffReducedWord(R!.diff2,order,x_inv*newD.states.names[d]*y);
        dd := Position(newD.states.names,wd);
        if dd <> fail then AddEdgeFSA(newD,[xx,yy],d,dd); fi;
      else wd := newD.states.names[dd];
      fi;
      dd_inv := TargetDFA(newD,[yy,xx],d_inv);
      if i=len then
        wd_inv := DiffReducedWord(R!.diff2,order,g^-1);
        if dd_inv<>0 and newD.states.names[dd_inv] <> wd_inv then
          DeleteEdgeFSA(newD,[yy,xx],d_inv,dd_inv); 
          InfoCorrectDiffMachine("Replacing edge to ",newD.states.names[dd_inv],
                        "by edge to ",wd_inv,"\n");
          dd_inv:= 0;
        fi;
        if dd_inv=0 then
          change:= true;
          dd_inv := Position(newD.states.names,wd_inv);
          if dd_inv <> fail then AddEdgeFSA(newD,[yy,xx],d_inv,dd_inv); fi;
        fi;
      elif dd_inv=0 then
        change := true;
      wd_inv := DiffReducedWord(R!.diff2,order,y_inv*newD.states.names[d_inv]*x);
        dd_inv := Position(newD.states.names,wd_inv);
        if dd_inv <> fail then AddEdgeFSA(newD,[yy,xx],d_inv,dd_inv); fi;
      else wd_inv := newD.states.names[dd_inv];
      fi;
      if dd=fail and dd_inv=fail then
        AddStateFSA(newD,wd);
        dd := newD.states.size;
     InfoCorrectDiffMachine2("Creating new state numbered ",dd," for ",wd,"\n");
        AddEdgeFSA(newD,[xx,yy],d,dd);
        if wd=wd_inv then
          dd_inv := dd;
          AddEdgeFSA(newD,[yy,xx],d_inv,dd_inv);
          inverses[dd] := dd;
        else
          AddStateFSA(newD,wd_inv);
          dd_inv := newD.states.size;
          InfoCorrectDiffMachine2(
                   "Creating new state numbered ",dd_inv," for ",wd_inv,"\n");
          AddEdgeFSA(newD,[yy,xx],d_inv,dd_inv);
          inverses[dd] := dd_inv;
          inverses[dd_inv] := dd;
        fi;
      elif dd_inv=fail then
        dd_inv := inverses[dd];
        AddEdgeFSA(newD,[yy,xx],d_inv,dd_inv); 
      elif dd=fail then
        dd := inverses[dd_inv];
        AddEdgeFSA(newD,[xx,yy],d,dd);
      fi;
      InfoCorrectDiffMachine2("dd ",dd," wd ",wd,"\n");
      InfoCorrectDiffMachine2("dd_inv ",dd_inv," wd_inv ",wd_inv,"\n");
      d := dd;
      d_inv := dd_inv;
      i := i+1;
    od;
    if change=false then
      InfoCorrectDiffMachine("No changes made to difference machine for ",triple,"\n");
    fi;
  od;
  R!.diff2 := newD;
end;

TestAutomatic := function(R)
  local WA, order,
    kb, waOK, gmOK, IdWord, i, gpaok;

  order := WordOrder(R);
  R!.options.tidyint := 20; 
  R!.options.maxeqns := 200;
  R!.options.maxstates := 1000;
  R!.options.outputWords := true; 
    # gpcheckmult should output a list of pairs of words 
    # it has found which don't fellow travel (but should).
   
  repeat
    kb := KBWD(R);
    if not kb and R!.options.maxeqns<262144 then
      if R!.options.tidyint=20 then R!.options.tidyint := 100;
      else R!.options.tidyint := 500; fi;
      if R!.options.maxeqns=200 then R!.options.maxeqns := 32768;
      else R!.options.maxeqns := 262144; fi;
      if IsBound(R!.options.maxstates) then Unbind(R!.options.maxstates); fi;
    elif not kb then 
      Print
   ("Repeated runs of KB failed to show stabilisation of word differences.\n");
      return false;
    fi;
  until kb=true;


  repeat
    if R!.ordering<>"shortlex" then 
      #Need to convert generators in R!.diff2.states
      R!.diff2 := SubstringClosure(R!.diff2,order,true);
      # and back again!
    fi;
    Info(InfoRWS,1,"Making word acceptor.\n");
    WA := WdAcceptor(R!.diff2,order);
    Info(InfoRWS,1,
        "Word acceptor has ",WA.states.size," states before minimization.\n");
    R!.wa := MinimizeFSA(WA);
    Info(InfoRWS,1,
      "Word acceptor has ",R!.wa.states.size," states after minimization.\n");
    Info(InfoRWS,2,"R!.wa := ",R!.wa,"\n");
    repeat
      waOK := GpGenMult(R); 
      Info(InfoRWS,1,"waOK ",waOK,"\n");
      if waOK then 
        InfoTestAutomatic("R!.gm := ",R!.gm,"\n");
        gmOK := GpCheckMult(R);
        Info(InfoRWS,1,"gmOK ",gmOK,"\n");
        if IsBound(R!.wg) then
          Info(InfoRWS,2,"R!.wg ",R!.wg,"\n");
          CorrectDiffMachine(R,order);
          Unbind(R!.wg);
          Unbind(R!.gm);
          Info(InfoRWS,1,"R!.diff2 now has ",R!.diff2.states.size," states.\n");
          Info(InfoRWS,2,"R!.diff2 := ",R!.diff2,"\n");
        fi;
      fi;
    until waOK=false or gmOK=true;
   until waOK;

   gpaok := GpAxioms(R);
   if gpaok then
      R!.isAvailableNormalForm := true;
      R!.isAvailableReduction := true;
      R!.isAvailableSize := true;
      R!.warningOn := false;
   fi;

   return gpaok;
end;
