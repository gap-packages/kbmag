#############################################################################
##
#A  correspondence.g          GAP library      Andrew Solomon and Derek Holt
##
## The functions in this file are for converting words between their
## external representations as elements of the free group/monoid/
## semigroup from which a rewriting system is defined and their
## internal representations as words in the WordMonoid od the rewriting
## system.
##
## Their are also functions for converting between internal words and
## lists of integers.
##
##

######################################################
##
##  fg.i corresponds with fm.gims[i]
##  (fg.i)^-1 corresponds with fm.iims[i]
##   Returns a record with these four components
####################################################
CorrespondenceGroupMonoid:= function (fg, fm, gims, iims)
local r;
  r:=rec(freegms := fg, freemonoid := fm, genims := gims,
    invims := iims,
    backnums:=[]
    );
  # assign in backnums the group generators numbers corresponding to monoid
  # generator numbers. Assign the inverses first, for nice involution
  # treatment.
  r.backnums{iims}:=-[1..Length(gims)];
  r.backnums{gims}:=[1..Length(gims)];
  return r;
end;

##We need also a simpler function of the same type.
CorrespondenceMSMonoid:=
#The first argument can be a free semigroup or a free monoid.
function (fs, fm)
  return rec(freegms := fs, freemonoid := fm);
end;

############################################################
## Using a correspondence as defined above, converts
## an element of the free group to an elt of the free monoid
###########################################################
FreeGroup2FreeMonoid := function(corr, elt)
  local
      res,
      gens,
      i, 
      x;

  x:=ShallowCopy(LetterRepAssocWord(elt));
  for i in [1..Length(x)] do
    if x[i]<0 then
      x[i]:=corr.invims[-x[i]];
    else
      x[i]:=corr.genims[x[i]];
    fi;
  od;
  return AssocWordByLetterRep(FamilyObj(One(corr.freemonoid)),x);
end;

############################################################
## Using a correspondence as defined above, converts
## an element of the free monoid to an elt of the free group
###########################################################
FreeMonoid2FreeGroup := function(corr, elt)
local w,wlist,i,l,t;

  wlist:=LetterRepAssocWord(elt);
  # translate back and free cancellation
  w:=[];
  l:=0;
  i:=1;
  while i<=Length(wlist) do
    t:=corr.backnums[wlist[i]];
    if l=0 or w[l]<>-t then
      l:=l+1;
      w[l]:=t;
    else
      l:=l-1;
    fi;
    i:=i+1;
  od;
  if l<Length(w) then
    w:=w{[1..l]};
  fi;
  return AssocWordByLetterRep(FamilyObj(One(corr.freegms)),w);
end;

#And the corresponding functions for the simpler cases.
FreeMS2FreeMonoid := function(corr, elt)
  local
      res,
      gens,
      i, 
      x;

  x:=LetterRepAssocWord(elt);
  return AssocWordByLetterRep(FamilyObj(One(corr.freemonoid)),x);
end;

FreeMonoid2FreeMS := function(corr, elt)
  local
      res,
      gens,
      i, 
      x;

  x := ExtRepOfObj(elt);

  if HasOne(corr.freegms) then
    gens := GeneratorsOfMonoid(corr.freegms);
    if Length(x)=0 then
      return Identity(corr.freegms);
    fi;
  else
    gens := GeneratorsOfSemigroup(corr.freegms);
    if Length(x)=0 then
      Error("Cannot map empty word into a semigroup");
    fi;
  fi;

  res := gens[x[1]]^x[2];

  for i in [3,5 .. Length(x)-1] do
    res := res*gens[x[i]]^x[i+1];
  od;

  return res;
end;


## The last two functions are for converting between words in the
## WordMonoid of a rewriting system and lists of integers.
##
#############################################################################
##
#F  WordToListRWS( <w>, <gens> ) .  converts word to list of integers
##
## <w> should be a word in the generators contained in the list <gens>,
## a list of ng elements of a free group, semigroup or monoid,
## The corresponding list of integers is computed an returned.
WordToListRWS := LetterRepAssocWord;

#############################################################################
##
#F  ListToWordRWS( <l>, gens ) .  converts list of integers to word
##
## <l> should be a list of integers in range [1..<ng>], where gens
## is a list of ng elements of a free group, semigroup or monoid,
## and IdWord is the identity of that structure if it exists, and
## false otherwise.
## The corresponding word in the generators in <gens> is computed.
ListToWordRWS := function ( l, gens )
  return AssocWordByLetterRep(FamilyObj(gens[1]),l,gens);
end;


#############################################################################
##
#F  StringRWS( <w> ) . . . . . . .  converts word to string
##
## Same as String except when w  = identity, when outputs "IdWord"
## Necessary for compatibility with GAP3 interface.
StringRWS := function(w)
   if Length(w)=0
     then return "IdWord";
   fi;
   return String(w);
end;
