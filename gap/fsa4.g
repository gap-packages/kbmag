#############################################################################
##
#A  fsa4.g                  GAP library                  Derek Holt
##
##  1.3.00. created this file from GAP3 version fsa.g and started adapting
##  it to GAP4.
##
##  24/9/98 - corrected dreadful bug in DeleteStateFSA
##  This file contains those functions that deal with finite state automata.
##
## 1.5.96. - code added to deal with the new "list of words" and
## "list of integers" set-record types.
##
DeclareInfoClass("InfoFSA");
#############################################################################
#V  _RWST_                external variable - temporary name of list of strings
#V  _FSA		  external variable - finite state automaton
#V  _FSA_determinize	  external variable -determinized finite state automaton
#V  _FSA_min		  external variable - minimized finite state automaton
#V  _FSA_not		  external variable - `not' finite state automaton
#V  _FSA_star		  external variable - `star' finite state automaton
#V  _FSA_reverse	  external variable - `reverse' finite state automaton
#V  _FSA_exists	  	  external variable - `exists' finite state automaton
#V  _FSA_swap_coords  	  external variable - `swap' finite state automaton
#V  _FSA_and  	  	  external variable - `and' finite state automaton
#V  _FSA_or  	  	  external variable - `or' finite state automaton
#V  _FSA_concat	 	  external variable - `concat' finite state automaton
_RWST_ := [];
_FSA := rec();
_FSA_determinize := rec();
_FSA_min := rec();
_FSA_not := rec();
_FSA_star := rec();
_FSA_reverse := rec();
_FSA_exists := rec();
_FSA_swap_coords := rec();
_FSA_and := rec();
_FSA_or := rec();
_FSA_concat := rec();
_KBExtDir  :=  DirectoriesPackagePrograms("kbmag");
_KBTmpFileName := TmpName();

#############################################################################
##
#F  IsFSA(<x>) . . . . . . . test whether x is an fsa
##
##  Public function.
IsFSA := function ( x )
    return IsRecord(x) and IsBound(x.isFSA) and x.isFSA; 
end;

#############################################################################
##
#F  IsInitializedFSA(<x>) . . . . . . . test whether x is an initialized fsa
##
##  Public function.
IsInitializedFSA := function ( x )
    return IsRecord(x) and IsBound(x.isInitializedFSA) and x.isInitializedFSA; 
end;

#############################################################################
##
#F  ExpandFieldSR(<list>) . . expand a sparsely stored name list
##
##  ExpandFieldSR takes a sparse <list> as argument and
##  returns the corresponding dense list (which may have gaps).
##  e.g. [[1,2],[3,4]] produces output [2,,4].
##
##  Private function.
ExpandFieldSR := function ( list )
    local newlist, term;
    newlist := [];
    for term in list do
      newlist[term[1]] := term[2];
    od;
    return newlist;
end;

#############################################################################
##
#F  InitializeSR(<sr>) . . . . . . . initialize a set-record
##
##  <sr> should be a set-record conforming to the criteria.
##  The criteria are checked, various other fields are calculated and set,
##  and the existing fields are (partially) checked for validity.
##
##  Public function.
InitializeSR := function ( sr )
  local  i, j, k, s, ba, lba, nv, fld;
    if not IsBound(sr.type) or not IsBound(sr.size) then
       Error("Subfield 'type' or 'size' of set-record field is not set.");
    fi;
    
    if IsBound(sr.base) then
      InitializeSR(sr.base);
    fi;
    if IsBound(sr.labels) then
      InitializeSR(sr.labels);
    fi;

    # if the set record names are stored in sparse format, we
    # convert to dense format for internal use - they will still be
    # printed in sparse format.
    k := sr.type;
    if k="words" or k="identifiers" or k="strings" or
                    k="list of words" or k="list of integers" then
      if not IsBound(sr.format) or not IsBound(sr.names)
                                        or not IsList(sr.names) then
         Error(
  "Subfield 'format' or 'names' of set-record field is not set or invalid.");
      fi;
      sr.printingFormat := sr.format;
      if sr.format="sparse" then
         sr.format := "dense";
         sr.names := ExpandFieldSR(sr.names);
      fi;
    fi;

    if k="words" or k="list of words" then
      if not IsBound(sr.alphabet) or not IsList(sr.alphabet) then
         Error(
  "Subfield 'alphabet' of set-record field is not set or invalid.");
      fi;
    fi;

    if k="labeled" or k="labelled" then
      if not IsBound(sr.format)
         or not IsBound(sr.labels) or not IsRecord(sr.labels)
         or not IsBound(sr.setToLabels) or not IsList(sr.setToLabels) then
         Error(
           "Some required field for type \"labeled\"  is not set or invalid.");
      fi;
      sr.printingFormat := sr.format;
      if  sr.format="sparse" then
        sr.format := "dense";
        sr.setToLabels := ExpandFieldSR(sr.setToLabels);
      fi;
    fi;

    if k="product" then
      if not IsBound(sr.padding) or not IsBound(sr.arity)
          or not IsBound(sr.base) or not IsRecord(sr.base)  then
         Error("Some required field for type \"product\" is not set.");
      fi;
      if IsBound(sr.base.names) then
    # calculate names of set-record members
        ba := Concatenation(sr.base.names,[sr.padding]);
        lba := Length(ba);
        nv := sr.arity; 
        sr.names := [];
        fld := sr.names;
        s := sr.size;
        for i in [1..s] do
          fld[i]:=[];
          k := i-1;
          for j in Reversed([1..nv]) do
            fld[i][j] := ba[k mod lba + 1];
              k := Int(k/lba);
          od;
        od;
      fi;
    fi;

end;

#############################################################################
##
#F  InitializeFSA(<fsa>) . . . . . . . initialize an fsa
##
##  <fsa> should be an fsa-record conforming to the criteria.
##  The criteria are checked, various other fields are calculated and set,
##  and the existing fields are (partially) checked for validity.
##  The entries in the flag field ("DFA", "minimized", "BFS", etc.)
##  are assumed to be valid if set.
##  
##  Public function.
InitializeFSA := function ( fsa )
    local ns, ne, i, j;
 # First check that the fsa has the 7 compulsory fields.
    if not IsFSA(fsa) then
       Error("Argument is not an fsa.");
    fi;
    if IsBound(fsa.isInitialized) and fsa.isInitializedFSA = true then
       Print("This fsa is already initialized.\n");
       return;
    fi;
    if not IsBound(fsa.alphabet) or not IsRecord(fsa.alphabet) then
       Error("'alphabet' field is not set, or invalid.");
    fi;
    if not IsBound(fsa.states) or not IsRecord(fsa.states) then
       Error("'states' field is not set, or invalid.");
    fi;
    if not IsBound(fsa.initial) or not IsList(fsa.initial) then
       Error("'initial' field is not set, or invalid.");
    fi;
    if not IsBound(fsa.accepting) or not IsList(fsa.accepting) then
       Error("'accepting' field is not set, or invalid.");
    fi;
    if not IsBound(fsa.table) or not IsRecord(fsa.table) then
       Error("'table' field is not set, or invalid.");
    fi;
    if not IsBound(fsa.flags) or not IsList(fsa.flags) then
       Error("'flags' field is not set, or invalid.");
    fi;

    InitializeSR(fsa.states);
    InitializeSR(fsa.alphabet);

    ns := fsa.states.size;
    ne := fsa.alphabet.size;

    fsa.initial := Set(fsa.initial);
    fsa.accepting := Set(fsa.accepting);
    fsa.flags := Set(fsa.flags);

    if not IsBound(fsa.table.format) or not IsBound(fsa.table.transitions) then
       Error("Subfield 'format' or 'transitions' of table field is not set.");
    fi;
    fsa.table.printingFormat := fsa.table.format;
    if fsa.table.format = "dense nondeterministic" then
	Error("Sorry - dense nondeterministic tables not yet supported.");
    elif fsa.table.format = "dense deterministic" then
      fsa.denseDTable := fsa.table.transitions;
      if Length(fsa.denseDTable) <> ns then
        Error("Length of transition table wrong.");
      fi;
      for i in [1..ns] do
        for j in [1..ne] do
          if not IsBound(fsa.denseDTable[i][j]) then
            fsa.denseDTable[i][j] := 0;
          fi;
        od;
      od;
    elif fsa.table.format = "sparse" then
      fsa.sparseTable := fsa.table.transitions;
      if Length(fsa.sparseTable) <> ns then
        Error("Length of transition table wrong.");
      fi;
    else
      Error("Invalid transition table format.");
    fi; 
    
    fsa.isInitializedFSA := true;
end;

#############################################################################
##
#F  FSA(alphabet) . . . . . . . make an initialized FSA with a 
##  specified alphabet and a single state which is both accepting and initial
##
##  Public function.
FSA := function ( alphabet )
    local F;
    F := rec(); 
    F.isFSA := true;
    F.alphabet := alphabet;
    F.states := rec(type := "simple",size := 1);
    F.flags := ["DFA"];
    F.initial := [1];
    F.accepting := [1];
    F.table := rec(
      format := "dense deterministic",
      numTransitions := 0,
         transitions := [0 * [1..alphabet.size]]
    );
    InitializeFSA(F); 

    return F; 
end;

#############################################################################
#F  AlphabetFSA 
##
##  Public function.
AlphabetFSA := fsa -> fsa.alphabet;

#############################################################################
#F  StatesFSA 
##
##  Public function.
StatesFSA := fsa -> fsa.states;

#############################################################################
#F  NumberOfStatesFSA 
##
##  Public function.
NumberOfStatesFSA := fsa -> fsa.states.size;

#############################################################################
#F  NumberOfLettersFSA
#F  SizeOfAlphabetFSA
##
##  Public function.
NumberOfLettersFSA := fsa -> fsa.alphabet.size;
SizeOfAlphabetFSA := fsa -> fsa.alphabet.size;

#############################################################################
##
#F  IsDeterministicFSA(<fsa>) . . . . . . . test if fsa is deterministic
##
##  Tests if the fsa <fsa> is deterministic.
##  The definition of deterministic used here is that of a partial
##  deterministic finite state automaton, rather than a total one.
##  This means, no epsilon-transtions, *at most* one initial state and
##  *at most one* transition from any state with a given label.
##  An FSA is is non-deterministic (NFA) if one of these conditions fails.
##
##  Public function.
IsDeterministicFSA := function ( fsa )
    local term, subterm, dfa_check;
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if "DFA" in fsa.flags then
      return true;
    fi;
    if "NFA" in fsa.flags then
      return false;
    fi;
    if Length(fsa.initial) > 1 then
      AddSet(fsa.flags,"NFA");
      return false;
    fi;
    if IsBound(fsa.denseDTable) then
 # This must imply DFA
      AddSet(fsa.flags,"DFA");
      return true;
    fi;
    for term in fsa.sparseTable do
    # sparseTable must be bound at this point
      dfa_check:=[];
      for subterm in term do
        if subterm[1]=0 or subterm[1]="epsilon" or
             IsBound(dfa_check[subterm[1]]) then
          AddSet(fsa.flags,"NFA");
          return false;
        else
          dfa_check[subterm[1]] := 1;
        fi;
      od;
    od;

    AddSet(fsa.flags,"DFA");
    return true;
end;

#############################################################################
##
#F  SparseTableToDenseDTableFSA(<fsa>) . . get DenseDTable from SparseTable
##  SparseTableToDenseDTableFSA calculates the DenseDTable of the fsa from
##  the SparseTable and  returns it.
##
##  Private function.
SparseTableToDenseDTableFSA := function ( fsa )
    local denseDTable, sparseTable, row, newrow, dt, ne, term, i;
    ne := fsa.alphabet.size;
    sparseTable := fsa.sparseTable;
    if IsBound(fsa.table.defaultTarget) then
      dt:=fsa.table.defaultTarget;
    else
      dt:=0;
    fi;
    denseDTable := [];
    for row in sparseTable do
      newrow:=[];
      for i in [1..ne] do newrow[i]:=dt; od;
      for term in row do
        if term[1]=0 or newrow[term[1]] <> dt then
          AddSet(fsa.flags,"NFA");
       Error("This fsa is nondeterministic, so cannot create DenseDTable.\n");
        fi;
        newrow[term[1]]:=term[2];
      od;
      Add(denseDTable,newrow);
    od;
    return denseDTable;
end;

#############################################################################
##
#F  DenseDTableToSparseTableFSA(<fsa>) . . get SparseTable from DenseDTable
##  DenseDTableToSparseTableFSA calculates the SparseTable of the fsa
##  from the DenseDTable and returns it.
##
##  Private function.
DenseDTableToSparseTableFSA := function ( fsa )
    local denseDTable, sparseTable, row, newrow, dt, ne, i;
    ne := fsa.alphabet.size;
    denseDTable := fsa.denseDTable;
    if IsBound(fsa.table.defaultTarget) then
      dt:=fsa.table.defaultTarget;
    else
      dt:=0;
    fi;
    sparseTable := [];
    for row in denseDTable do
      newrow:=[];
      for i in [1..ne] do
        if row[i] <> dt then
          Add(newrow,[i,row[i]]);
        fi;
      od;
      Add(sparseTable,newrow);
    od;
    return sparseTable;
end;

#############################################################################
##
#F  DenseDTableToBackTableFSA(<fsa>)  . . . . get BackTable from DenseDTable
##  DenseDTableToBackTableFSA calculates the BackTable of the fsa from the
##  DenseDTable and  returns it.
##
##  Private function.
DenseDTableToBackTableFSA := function ( fsa )
    local denseDTable, backTable, row, ne, ns, i, j;
    ne := fsa.alphabet.size;
    ns := fsa.states.size;
    denseDTable := fsa.denseDTable;
    backTable := [];
    for i in [1..ns] do
      backTable[i] := [];
    od;
    for i in [1..ns] do
      row := denseDTable[i];
      for j in [1..ne] do
        if row[j] in [1..ns] then
          Add(backTable[row[j]],[j,i]);
        fi;
      od;
    od;
    return backTable;
end;

#############################################################################
##
#F  SparseTableToBackTableFSA(<fsa>)  . . . . get BackTable from SparseTable
##  SparseTableToBackTableFSA calculates the BackTable of the fsa from
##  the SparseTable and returns it.
##  The backTable still does not include "default-target" edges.
##
##  Private function.
SparseTableToBackTableFSA := function ( fsa )
    local sparseTable, backTable, row, ne, ns, i, term;
    ne := fsa.alphabet.size;
    ns := fsa.states.size;
    sparseTable := fsa.sparseTable;
    backTable := [];
    for i in [1..ns] do
      backTable[i] := [];
    od;
    for i in [1..ns] do
      row := sparseTable[i];
      for term in row do
        if term[2] in [1..ns] then
          Add(backTable[term[2]],[term[1],i]);
        fi;
      od;
    od;
    return backTable;
end;

#############################################################################
##
#F  DenseDTableFSA(<fsa>) . . . . . . . calculates DenseDTable of dfa
##  DenseDTableFSA calculates the DenseDTable of the fsa <fsa> and returns it.
##  Public function.
DenseDTableFSA := function ( fsa )
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if not IsBound(fsa.denseDTable) then
       fsa.denseDTable := SparseTableToDenseDTableFSA(fsa);
    fi;
    return fsa.denseDTable;
end;
    

#############################################################################
##
#F  SparseTableFSA(<fsa>) . . . . . . . calculates DenseDTable of fsa
##  SparseTableFSA calculates the SparseTable of the fsa and returns it.
##  Public function.
SparseTableFSA := function ( fsa )
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if not IsBound(fsa.sparseTable) then
       fsa.sparseTable := DenseDTableToSparseTableFSA(fsa);
    fi;
    return fsa.sparseTable;
end;

#############################################################################
##
#F  BackTableFSA(<fsa>) . . . . . . . calculates BackTable of fsa
##  BackTableFSA calculates the BackTable of the fsa and returns it.
##  If calculated from the SparseTable, it will not include "default-target"
##  edges.
##  Public function.
BackTableFSA := function ( fsa )
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if not IsBound(fsa.backTable) then
       if IsBound(fsa.denseDTable) then
         fsa.backTable := DenseDTableToBackTableFSA(fsa);
       else
         fsa.backTable := SparseTableToBackTableFSA(fsa);
       fi;
    fi;
    return fsa.backTable;
end;

#############################################################################
##
#F  LinePrintFSA(<line> [,<filename>]) . . . . . . . print the line x
##
##  LinePrintFSA prints the line (a string) to the terminal (default)
##  or to file filename  if specified, formatting nicely.
##  It works by building up the material to be printed line by line as strings,
##  and calling LinePrintFSA to print each individual line.
##
LinePrintFSA := function ( arg )
    local line, filename;
    line := arg[1];
    if Length(arg) = 1 then filename := "";
    else filename := arg[2];
    fi; if filename = "" then Print(line,"\n");
    else AppendTo(filename,line,"\n");
    fi;
end;

#############################################################################
##
#F  WordToStringSR( <word>, <gens>, <names> )
##                                     . . . . . converts <word> to a string
##
## <word> is a word in generators <gens>.
## <names> is a list of printing strings for <gens>.
## The word is converted into a string representing the word for printing.
WordToStringSR := function ( word, gens, names )
   local string, i, l, ls, ng, g, ct, lg;
   l := Length(word);
   if l=0 then
      return "IdWord";
   fi;
   string := "";
   lg := 0; ct := 0;
   for i in [1..l] do
     g := Position(gens,Subword(word,i,i));
     if g <> lg and lg <> 0 then
        if string<>"" then string := Concatenation(string,"*"); fi;

        ng := names[lg];
        if ct > 1 then
           #Check to see if names[lg] ends "^-1"
           ls := Length(ng);
           if ls>3 and ng[ls-2]='^' and ng[ls-1]='-' and ng[ls]='1' then
             string := Concatenation(string,ng{[1..ls-1]},String(ct));
           else
             string := Concatenation(string,ng,"^",String(ct));
           fi;
        else string := Concatenation(string,ng);
        fi;
        ct := 0;
     fi;
     lg := g; ct := ct+1;
   od;
   if string<>"" then string := Concatenation(string,"*"); fi;
   ng := names[lg];
   if ct > 1 then
       #Check to see if names[lg] ends "^-1"
       ls := Length(ng);
       if ls>3 and ng[ls-2]='^' and ng[ls-1]='-' and ng[ls]='1' then
         string := Concatenation(string,ng{[1..ls-1]},String(ct));
       else
         string := Concatenation(string,ng,"^",String(ct));
       fi;
   else string := Concatenation(string,ng);
   fi;

   return string;
end;

#############################################################################
##
#F  WriteSetRecordSR(<sr> [<name>, <filename>, <offset>, <endsymbol>])
##                                  . . print the set record <sr>
##
##  WriteSetRecordSR prints the set record <sr> to the terminal (default)
##  or to file <filename> if specified, formatting nicely.
##  It works by building up the material to be printed line by line as strings,
##  and calling LinePrintFSA to print each individual line.
##  If the optional string <name> is present, printing is preceded by an
##  assignment "name:=", so that the resulting file can be read back in.
##  if the optional positive integer <offset> is present then each line
##  is preceded by <offset> spaces.
##  If the optional string <endsymbol> is present, then this is printed at
##  the end (it is likely to be ";" or ",").
##
##  Private function.
WriteSetRecordSR := function ( arg )
    local  sr, filename, name, offset, endsymbol, offstring, line, ct, first,
	   pn,  wstring, i, tempfn, ids;
    sr := arg[1];
    if (sr.type="identifiers" or sr.type="words" or sr.type="list of words")
         and not IsBound(sr.printingStrings) then
    ## To find out what the printing strings should be, the only way is to
    ## output the identifiers as strings to a temporary file and read back in.
       tempfn:=TmpName();
       if sr.type="identifiers" then
         ids:=sr.names;
       else
         ids:=sr.alphabet;
       fi;
       PrintTo(tempfn,"_RWST_:=[");
       for i in [1..Length(ids)] do
         if i>1 then AppendTo(tempfn,","); fi;
         AppendTo(tempfn,"\"",ids[i],"\"");
       od;
       AppendTo(tempfn,"];\n");
       Read(tempfn);
       sr.printingStrings:=_RWST_;
       Exec(Concatenation("/bin/rm -f ",tempfn));
    fi; 
    filename := "";
    name := "";
    endsymbol := "";
    offset:=0;
    if Length(arg)>=2 then
      name := arg[2];
    fi;
    if Length(arg)>=3 then
      filename := arg[3];
    fi;
    if Length(arg)>=4 then
      offset := arg[4];
    fi;
    if Length(arg)>=5 then
      endsymbol := arg[5];
    fi;
    if not IsInt(offset) or offset<=0 then
       offset := 0;
    fi;
    offstring := String("",offset);
    if name = "" then
      line := "rec (";
    else
      line := Concatenation(String(name,16+offset-4)," := rec (");
    fi;
    LinePrintFSA(line,filename);

    line := Concatenation(offstring,String("type",16),
                                                 " := ","\"",sr.type,"\"",",");
    LinePrintFSA(line,filename);
    line := Concatenation(offstring,String("size",16)," := ",String(sr.size));
    if sr.type <> "simple" then
      line := Concatenation(line,",");
    fi;
    LinePrintFSA(line,filename);
    if sr.type = "product" then
      line:=Concatenation(offstring,String("arity",16)," := ",
							String(sr.arity),",");
      LinePrintFSA(line,filename);
      line:=Concatenation(offstring,String("padding",16)," := _,");
      LinePrintFSA(line,filename);
      WriteSetRecordSR(sr.base,"base",filename,offset+4);
    elif sr.type="words" or sr.type="identifiers" or sr.type="strings"
         or sr.type="list of words" or  sr.type="list of integers" then
      if sr.type="strings" then
        pn := [];
        for i in [1..sr.size] do
           pn[i] := Concatenation("\"",sr.names[i],"\"");
        od;
      elif sr.type="words" or sr.type="identifiers" or
           sr.type="list of words" then 
        pn := sr.printingStrings;
      fi;
      if sr.type="words"  or sr.type="list of words" then
        line := Concatenation(offstring,String("alphabet",16)," := [");
        ct := 1;
        while ct <= Length(sr.alphabet) do
          if ct=1 or Length(line)+Length(pn[ct]) <= 76 then
            if ct > 1 then
               line := Concatenation(line,",");
            fi;
            line := Concatenation(line,pn[ct]);
          else
            line := Concatenation(line,",");
            LinePrintFSA(line,filename);
            line := String("",21+offset);
            line := Concatenation(line,pn[ct]);
          fi;
          ct := ct+1;
        od;
        line := Concatenation(line,"],");
        LinePrintFSA(line,filename);
      fi;
      line := Concatenation(offstring,String("format",16)," := ");
      line := Concatenation(line,"\"",sr.printingFormat,"\"",",");
      LinePrintFSA(line,filename);
      line := Concatenation(offstring,String("names",16)," := [");
      if sr.printingFormat="dense" then
 # recall that the names are always stored internally in dense format.
        ct := 1;
        while ct <= sr.size do
          if sr.type="words" then
            wstring := WordToStringSR(sr.names[ct],sr.alphabet,pn);
          elif sr.type="list of words" then
            wstring:="[";
            for i in [1..Length(sr.names[ct])] do
              if i>1 then
                wstring:=Concatenation(wstring,",");
              fi;
              wstring:=Concatenation(wstring,
                 WordToStringSR(sr.names[ct][i],sr.alphabet,pn) );
            od;
            wstring:=Concatenation(wstring,"]");
          elif sr.type="list of integers" then
            wstring:="[";
            for i in [1..Length(sr.names[ct])] do
              if i>1 then
                wstring:=Concatenation(wstring,",");
              fi;
              wstring:=Concatenation(wstring,String(sr.names[ct][i]));
            od;
            wstring:=Concatenation(wstring,"]");
          else wstring := pn[ct];
          fi;
          if ct=1 or Length(line)+Length(wstring) <= 76 then
            if ct > 1 then
               line := Concatenation(line,",");
            fi;
            line := Concatenation(line,wstring);
          else
            line := Concatenation(line,",");
            LinePrintFSA(line,filename);
            line := String("",21+offset);
            line := Concatenation(line,wstring);
          fi;
          ct := ct+1;
        od;
        line := Concatenation(line,"]");
        LinePrintFSA(line,filename);
      else
        ct := 1;
        first := true;
        while ct <= sr.size do
          if IsBound(sr.names[ct]) then
             if sr.type="words" then
                 wstring :=
                     WordToStringSR(sr.names[ct],sr.alphabet,pn);
             elif sr.type="list of words" then
               wstring:="[";
               for i in [1..Length(sr.names[ct])] do
                 if i>1 then
                   wstring:=Concatenation(wstring,",");
                 fi;
                 wstring:=Concatenation(wstring,
                   WordToStringSR(sr.names[ct][i],sr.alphabet,pn) );
               od;
               wstring:=Concatenation(wstring,"]");
             elif sr.type="list of integers" then
               wstring:="[";
               for i in [1..Length(sr.names[ct])] do
                 if i>1 then
                   wstring:=Concatenation(wstring,",");
                 fi;
                 wstring:=Concatenation(wstring,String(sr.names[ct][i]));
               od;
               wstring:=Concatenation(wstring,"]");
             else wstring := pn[ct];
             fi;
             if first then
               line := Concatenation
                     (line,"[",String(ct),",",wstring,"]");
               first := false;
             else
               line := Concatenation(line,",");
               LinePrintFSA(line,filename);
               line := String("",21+offset);
               line := Concatenation
                     (line,"[",String(ct),",",wstring,"]");
             fi;
          fi;
          ct := ct+1;
        od;
        LinePrintFSA(line,filename);
        line := Concatenation(String("",20+offset),"]");
        LinePrintFSA(line,filename);
      fi;
    elif sr.type = "labeled" or sr.type="labelled"  then
      WriteSetRecordSR(sr.labels,"labels",filename,offset+4,",");
      line := Concatenation(offstring,String("format",16)," := ");
      line := Concatenation(line,"\"",sr.printingFormat,"\"",",");
      LinePrintFSA(line,filename);
      line := Concatenation(offstring,String("setToLabels",16)," := [");
      if sr.printingFormat="dense" then
        ct := 1;
        while ct <= sr.size do
          if not IsBound(sr.setToLabels[ct]) then
            if ct>1 then
              line := Concatenation(line,",");
            fi;
          elif ct=1 or
           Length(line)+Length(String(sr.setToLabels[ct])) <= 76 then
            if ct > 1 then
               line := Concatenation(line,",");
            fi;
            line := Concatenation(line,String(sr.setToLabels[ct]));
          else
            line := Concatenation(line,",");
            LinePrintFSA(line,filename);
            line := String("",21+offset);
            line := Concatenation(line,String(sr.setToLabels[ct]));
          fi;
          ct := ct+1;
        od;
        line := Concatenation(line,"]");
        LinePrintFSA(line,filename);
      else
        ct := 1;
        first := true;
        while ct <= sr.size do
          if IsBound(sr.setToLabels[ct]) then
             if first then
               line := Concatenation
                     (line,"[",String(ct),",",String(sr.setToLabels[ct]),"]");
               first := false;
             else
               line := Concatenation(line,",");
               LinePrintFSA(line,filename);
               line := String("",21+offset);
               line := Concatenation
                     (line,"[",String(ct),",",String(sr.setToLabels[ct]),"]");
             fi;
          fi;
          ct := ct+1;
        od;
        LinePrintFSA(line,filename);
        line := Concatenation(String("",20+offset),"]");
        LinePrintFSA(line,filename);
      fi;
    elif sr.type <> "simple" then
       Error("Invalid type for set record.");
    fi;
    if name = "" then
      line := Concatenation(")",endsymbol);
    else 
      line := String(")",16+offset-4);
      line := Concatenation(line,endsymbol);
    fi;
    LinePrintFSA(line,filename);
end;

#############################################################################
##
#F  WriteFSA(<fsa> [<name>, <filename>, <endsymbol>]) . . print the fsa "fsa"
##
##  WriteFSA prints the fsa <fsa> to the terminal (default) or to
##  file <filename> if specified, formatting nicely.
##  It works by building up the material to be printed line by line as strings,
##  and calling LinePrintFSA to print each individual line.
##  If the optional string <name> is present, printing is preceded by an
##  assignment "name:=", so that the resulting file can be read back in.
##  If the optional string <endsymbol> is present, then this is printed at
##  the end (it is likely to be ";" or ",").
##
##  Public function.
WriteFSA := function ( arg )
    local  fsa, ns, ne, filename, name, tabletype, table, endsymbol,
           line, ct, first, i, j;
    fsa := arg[1];
    filename := "";
    name := "";
    endsymbol := "";
    if Length(arg)>=2 then
      name := arg[2];
    fi;
    if Length(arg)>=3 then
      filename := arg[3];
    fi;
    if Length(arg)>=4 then
      endsymbol := arg[4];
    fi;

    if not IsInitializedFSA(fsa) then
      InitializeFSA(fsa);
    fi;
    ns := fsa.states.size;
    ne := fsa.alphabet.size;
    if filename = "" and name = "" then
      Print("rec (\n");
    elif filename = "" and name <> "" then
      Print(name," := \nrec (\n");
    elif filename <> "" and name = "" then
      PrintTo(filename,"rec (\n");
    else
      PrintTo(filename,name," := \nrec (\n");
    fi;

    line := String("isFSA",16);
    line := Concatenation(line," := true,");
    LinePrintFSA(line,filename);

    WriteSetRecordSR(fsa.alphabet,"alphabet",filename,4,",");
    WriteSetRecordSR(fsa.states,"states",filename,4,",");

    line := String("flags",16);
    line := Concatenation(line," := [");
    first := true;
    for i in fsa.flags do
      if not first then
        line := Concatenation(line,",");
      fi;
      first := false;
      line := Concatenation(line,"\"",i,"\"");
    od;
    line := Concatenation(line,"],");
    LinePrintFSA(line,filename);

    line := String("initial",16);
    line := Concatenation(line," := [");
    ct := 1;
    while ct<= Length(fsa.initial) do
      if ct=1 or Length(line)+Length(String(fsa.initial[ct])) <= 76 then
        if ct > 1 then
           line := Concatenation(line,",");
        fi;
        line := Concatenation(line,String(fsa.initial[ct]));
      else
        line := Concatenation(line,",");
        LinePrintFSA(line,filename);
        line := String("",21);
        line := Concatenation(line,String(fsa.initial[ct]));
      fi;
      ct := ct+1;
    od;
    line := Concatenation(line,"],");
    LinePrintFSA(line,filename);

    line := String("accepting",16);
    line := Concatenation(line," := [");
    ct := 1;
    if ns>1 and fsa.accepting=[1..ns] then
       line := Concatenation(line,"1..",String(ns));
    else
      while ct<= Length(fsa.accepting) do
        if ct=1 or Length(line)+Length(String(fsa.accepting[ct])) <= 76 then
          if ct > 1 then
             line := Concatenation(line,",");
          fi;
          line := Concatenation(line,String(fsa.accepting[ct]));
        else
          line := Concatenation(line,",");
          LinePrintFSA(line,filename);
          line := String("",21);
          line := Concatenation(line,String(fsa.accepting[ct]));
        fi;
        ct := ct+1;
      od;
    fi;
    line := Concatenation(line,"],");
    LinePrintFSA(line,filename);
    
    tabletype := fsa.table.printingFormat;

    if tabletype="dense deterministic"  then
      if IsDeterministicFSA(fsa) = false then
        fsa.table.printingFormat := "sparse"; 
        tabletype := fsa.table.printingFormat;
      elif not IsBound(fsa.denseDTable) then
        DenseDTableFSA(fsa);
      fi;
    fi;
    if tabletype="sparse" and not IsBound(fsa.sparseTable) then
      SparseTableFSA(fsa);
    fi;
    if tabletype="dense deterministic" then
      table := fsa.denseDTable;
      fsa.table.format := "dense deterministic";
 # Calculate number of nontrivial transitions
      ct := 0;
      for i in [1..ns] do
        for j in [1..ne] do
          if table[i][j] <> 0 then
            ct := ct+1;
          fi;
        od;
      od;
    else
      table := fsa.sparseTable;
      fsa.table.format := "sparse";
 # Calculate number of nontrivial transitions
      ct := 0;
      for i in [1..ns] do
        ct := ct + Length(table[i]);
      od;
    fi;
    fsa.table.numTransitions := ct;

    line := Concatenation(String("table",16)," := rec(");
    LinePrintFSA(line,filename);
    line := Concatenation(String("format",20),
                                      " := ","\"",fsa.table.format,"\"",",");
    LinePrintFSA(line,filename);
    line := Concatenation(String("numTransitions",20)," := ",
                           String(fsa.table.numTransitions),",");
    LinePrintFSA(line,filename);
    if tabletype = "sparse" and IsBound(fsa.table.defaultTarget) then
      line := Concatenation(line,String("defaultTarget",20)," := ");
      line := Concatenation(line,String(fsa.table.defaultTarget),",");
      LinePrintFSA(line,filename);
    fi;
    line := Concatenation(String("transitions",20)," := [");
    if ns=0 then
      LinePrintFSA(line,filename);
    fi;
    first := true;
    for i in [1..ns] do
      if first then
        line := Concatenation(line,"[");
        first := false;
      else
        line := Concatenation(String("",25),"[");
      fi;
      ct := 1;
      while ct<= Length(table[i]) do
        if ct=1 or Length(line)+Length(String(table[i][ct])) <= 76 then
          if ct > 1 then
             line := Concatenation(line,",");
          fi;
          line := Concatenation(line,String(table[i][ct]));
        else
          line := Concatenation(line,",");
          LinePrintFSA(line,filename);
          line := String("",25);
          line := Concatenation(line,String(table[i][ct]));
        fi;
        ct := ct+1;
      od;
      line := Concatenation(line,"]");
      if i<ns then
        line := Concatenation(line,",");
      fi;
      LinePrintFSA(line,filename);
    od;
    line := Concatenation(String("",20),"]");
    LinePrintFSA(line,filename);
    line := Concatenation(String("",16),")");
    LinePrintFSA(line,filename);

    line := Concatenation(")",endsymbol);
    LinePrintFSA(line,filename);
end;

#############################################################################
##
#F  ElementNumberSR(<sr>, <el>)  . . . get number of set-record element.
##
##  <sr> should be a set-record. <el> should either be a positive integer
##  representing an element of <sr> or a name for such an element.
##  In either case, the number of the element is returned.
##  False is returned if <el> is invalid.
##
##  Private function.
ElementNumberSR := function ( sr, el )
  local IdWord;
  if IsAssocWordWithOne(el) then
    IdWord := el^0;
  else IdWord := false;
  fi;
  if IsInt(el) then
    if el>sr.size+1 then
      return false;
    else
      return el;
    fi;
  elif el=IdWord then
    return sr.size+1;
  elif IsBound(sr.names) then
    return Position(sr.names,el);
  else
    return false;
  fi;
end;

#############################################################################
##
#F  TargetDFA(<fsa>,<e>,<s>) . . . . . . . target of edge in a dfa
##  TargetDFA calculates  and returns the target of the edge in the dfa <fsa>
##  with edge <e> and source-state <s>.
##  0 is returned if there is no edge.
##  <e> can either be the number of an edge or an edge-name.
##  <s> can either be the number of a state or a state-name.
##  The returned value has same type as <s> (or 0).
##  Public function.
TargetDFA := function ( fsa,e,s )
    local tname, term, row, ns, t, ng;
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if IsDeterministicFSA(fsa)=false  then
       Error("First argument is not a dfa.");
    fi;
    if IsList(e) then
      ng := fsa.alphabet.base.size;
      e := (ElementNumberSR(fsa.alphabet.base,e[1])-1) * (ng+1) + 
       ElementNumberSR(fsa.alphabet.base,e[2]);
    else 
      e := ElementNumberSR(fsa.alphabet,e);
    fi;
    if e=false then
      Error("Second argument is not a valid edge number or label.");
    fi;
    tname := not IsInt(s);
    s := ElementNumberSR(fsa.states,s);
    if s=false then
       Error("Third argument is not a valid state number or name.");
    fi;

    ns := fsa.states.size;
    if IsBound(fsa.denseDTable) then
      t := fsa.denseDTable[s][e];
      if t=0 then
        return 0;
      fi;
      if tname then
        return  fsa.states.names[t];
      fi;
      return t;
    fi;

    row := fsa.sparseTable[s];
    for term in row do
      if term[1]=e then
        t := term[2];
        if tname then
          if t=0 then
            return 0;
          fi;
          return fsa.states.names[t];
        fi;
        return t;
      fi;
    od;
    if IsBound(fsa.table.defaultTarget) then
      t := fsa.table.defaultTarget;
    else
      return 0;
    fi;
    if tname then
      if t=0 then
        return 0;
      fi;
      return fsa.states.names[t];
    fi;
    return t;

end;

#############################################################################
##
#F  TargetsFSA(<fsa>,<e>,<s>) . . . . . . . targets of edge
##  TargetsFSA calculates the targets of the edges in the fsa <fsa>
##  with edge <e> and source-state <s>.
##  The result is returned as a list of targets.
##  <l> can either be the number of an edge-label or an edge-label-name.
##  <s> can either be the number of a state or a state-name.
##  The members of the returned list have same type as <s>.
##  Public function.
TargetsFSA := function ( fsa,e,s )
    local tname, term, targets, row, ns, t, ng;
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if IsList(e) then
      ng := fsa.alphabet.base.size;
      e := (ElementNumberSR(fsa.alphabet.base,e[1])-1) * (ng+1) + 
       ElementNumberSR(fsa.alphabet.base,e[2]);
    else 
      e := ElementNumberSR(fsa.alphabet,e);
    fi;
    if e=false then
      Error("Second argument is not a valid edge number or label.");
    fi;
    tname := not IsInt(s);
    s := ElementNumberSR(fsa.states,s);
    if s=false then
       Error("Third argument is not a valid state number or name.");
    fi;

    ns := fsa.states.size;
    if IsBound(fsa.denseDTable) then
      if e=0 then
         return [];
      fi;
      t := fsa.denseDTable[s][e];
      if t=0 then
        return [];
      fi;
      if tname then
        return [ fsa.states.names[t] ];
      fi;
      return [ t ];
    fi;

    row := fsa.sparseTable[s];
    targets := [];
    for term in row do
      if term[1]=e then
        if tname then
          if term[2]>0 and term[2]<=ns then
            Add(targets,fsa.states.names[term[2]]);
          fi;
        else
          Add(targets,term[2]);
        fi;
      fi;
    od;
    if targets=[] and IsBound(fsa.table.defaultTarget) then
      if tname then
        Add(targets,fsa.states.names[fsa.table.defaultTarget]);
      else
        Add(targets,fsa.table.defaultTarget);
      fi;
    fi;
    return targets;

end;

#############################################################################
##
#F  SourcesFSA(<fsa>,<e>,<s>) . . . . . . . sources of edge
##  SourcesFSA calculates the sources of the edges in the fsa <fsa>
##  with edge <e> and source-state <s>.
##  The result is returned as a list of sources.
##  <l> can either be the number of an edge-label or an edge-label-name.
##  <s> can either be the number of a state or a state-name.
##  The members of the returned list have same type as <s>.
##  Public function.
SourcesFSA := function ( fsa,e,s )
    local tname, term, sources, row, ns, i, none, ng;
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if IsList(e) then
      ng := fsa.alphabet.base.size;
      e := (ElementNumberSR(fsa.alphabet.base,e[1])-1) * (ng+1) + 
       ElementNumberSR(fsa.alphabet.base,e[2]);
    else 
      e := ElementNumberSR(fsa.alphabet,e);
    fi;
    if e=false then
      Error("Second argument is not a valid edge number or label.");
    fi;
    tname := not IsInt(s);
    s := ElementNumberSR(fsa.states,s);
    if s=false then
       Error("Third argument is not a valid state number or name.");
    fi;

  #We need the backTable for this.
    BackTableFSA(fsa);
    row := fsa.backTable[s];
    sources := [];
    ns := fsa.states.size;
    for term in row do
      if term[1]=e then
        if tname then
          if term[2]>0 and term[2]<=ns then
            Add(sources,fsa.states.names[term[2]]);
          fi;
        else
          Add(sources,term[2]);
        fi;
      fi;
    od;
    if IsBound(fsa.table.defaultTarget) and fsa.table.defaultTarget=s and
          IsBound(fsa.sparseTable) then
    # there may be some "default-target" edges.
       for i in [1..ns] do
         row := fsa.sparseTable[i];
         none := true;
         for term in row do
           if term[1]=e then none:=false; fi;
         od;
         if none then
           Add(sources,i);
         fi;
       od;
       sources := Set(sources);
    fi;
    return sources;
end;

#############################################################################
##
#F  IsAcceptedWordDFA(<fsa>,<w>) . . . . . . . tests if word accepted by fsa
##  IsAcceptedWordDFA tests whether the word <w> is accepted by the
##  deterministic fsa <fsa>, and returns true or false.
##  <w> can either be a list of labels or a list of label numbers,
##  or a word in the labels for <fsa>.
##  (In the last case, the labels must be abstract generators.)
##  For an n-variable fsa, it can also be a list of n words (which will
##  be padded out at the end by the padding symbol).
##  Public function.
IsAcceptedWordDFA := function ( fsa,w )
    local state, label, len, iw, inw, nl, ps, ns, nv, i, pos, dead;
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if IsDeterministicFSA(fsa)=false then
       Error("Argument is not a dfa.");
    fi;
    if fsa.initial=[] then
      return false;
    fi;
    ns := fsa.states.size;
    state := fsa.initial[1];
    iw := IsWord(w);
    inw := false;
    if not iw and not IsList(w) then
      Error("Second argument must be a word or a list.");
    fi;
    if IsBound(fsa.alphabet.arity) and IsList(w) and IsWord(w[1]) then
      if not IsBound(fsa.alphabet.base.names) then
        Error("Can only span n-tuple of words if base-alphabet has names.");
      fi;
      if not IsBound(fsa.alphabet.padding) then
        Error("Can only span n-tuple of words if there is a padding symbol.");
      fi;
      ps := fsa.alphabet.padding;
      inw := true;
      nv := fsa.alphabet.arity;
      nl := [];
      for i in [1..nv] do
        nl[i] := Length(w[i]);
      od;
      len := Maximum(nl);
    elif iw then
      len := Length(w);
    else
      len := Length(w);
    fi;
    dead := false;
    pos := 1;
    while not dead and pos <= len do
      if inw then
         label := [];
         for i in [1..nv] do
           if pos <= nl[i] then
             label[i] := Subword(w[i],pos,pos);
           else
             label[i] := ps;
           fi;
         od;
      elif iw then
        label := Subword(w,pos,pos);
      else
        label := w[pos];
      fi;
      state := TargetDFA(fsa,label,state);
      if not state in [1..ns] then
        dead:=true;
      fi;
      pos := pos+1;
    od;
    if dead then
      return false;
    fi;
    return state in fsa.accepting;
end;

#############################################################################
##
#F  WordTargetDFA(<fsa>,<w>) . . . . . . . target of word under DFA
##  WordTargetDFA finds the target state when the word <w> is read by
##  the deterministic fsa <fsa>, and returns this state or 0.
##  <w> can either be a list of labels or a list of label numbers,
##  or a word in the labels for <fsa>.
##  (In the last case, the labels must be abstract generators.)
##  For an n-variable fsa, it can also be a list of n words (which will
##  be padded out at the end by the padding symbol).
##  Public function.
WordTargetDFA := function ( fsa,w )
    local state, label, len, iw, inw, nl, ps, ns, nv, i, pos, dead;
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if IsDeterministicFSA(fsa)=false then
       Error("Argument is not a dfa.");
    fi;
    if fsa.initial=[] then
      return 0;
    fi;
    ns := fsa.states.size;
    state := fsa.initial[1];
    iw := IsWord(w);
    inw := false;
    if not iw and not IsList(w) then
      Error("Second argument must be a word or a list.");
    fi;
    if IsBound(fsa.alphabet.arity) and IsList(w) and IsWord(w[1]) then
      if not IsBound(fsa.alphabet.base.names) then
        Error("Can only span n-tuple of words if base-alphabet has names.");
      fi;
      if not IsBound(fsa.alphabet.padding) then
        Error("Can only span n-tuple of words if there is a padding symbol.");
      fi;
      ps := fsa.alphabet.padding;
      inw := true;
      nv := fsa.alphabet.arity;
      nl := [];
      for i in [1..nv] do
        nl[i] := Length(w[i]);
      od;
      len := Maximum(nl);
    elif iw then
      len := Length(w);
    else
      len := Length(w);
    fi;
    dead := false;
    pos := 1;
    while not dead and pos <= len do
      if inw then
         label := [];
         for i in [1..nv] do
           if pos <= nl[i] then
             label[i] := Subword(w[i],pos,pos);
           else
             label[i] := ps;
           fi;
         od;
      elif iw then
        label := Subword(w,pos,pos);
      else
        label := w[pos];
      fi;
      state := TargetDFA(fsa,label,state);
      if not state in [1..ns] then
        dead:=true;
      fi;
      pos := pos+1;
    od;
    if dead then
      return 0;
    fi;
    return state;
end;

#############################################################################
##
#F  AddStateFSA(<fsa>[,<name>]) . . . . . . . adds state to an fsa
##  AddStateFSA adds a state to the end of the statelist of the fsa <fsa>.
##  It has the optional name or label <name> (but if the state-type is
##  "named", then the name must be supplied).
##  Public function.
AddStateFSA := function ( arg )
    local fsa, name, ns, new, i, dt;
    fsa := arg[1];
    if fsa.states.type = "product" then
      Error("Cannot alter a product-type state-list");
    fi;
    if Length(arg)=1 and IsBound(fsa.states.names) then
       Error("You must supply a name for the new state.");
    fi;
    name:="";
    if Length(arg)=2 then
      name:=arg[2];
    fi;
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    fsa.states.size := fsa.states.size+1;
    ns := fsa.states.size;
    if name<>"" and IsBound(fsa.states.names) then
        fsa.states.names[ns] := name;
    fi;
    if IsBound(fsa.denseDTable) then
      if IsBound(fsa.table.defaultTarget) then
        dt := fsa.table.defaultTarget;
      else
        dt := 0;
      fi;
      new:=[];
      for i in [1..fsa.alphabet.size] do new[i]:=dt; od;
      Add(fsa.denseDTable,new);
    fi;
    if IsBound(fsa.sparseTable) then
      new:=[];
      Add(fsa.sparseTable,new);
    fi;
    Unbind(fsa.backTable);
    RemoveSet(fsa.flags,"minimized");
    RemoveSet(fsa.flags,"trim");
    RemoveSet(fsa.flags,"accessible");
end;

#############################################################################
##
#F  DeleteListFSA(<l>,<n>) . . . . . . . delete element from list
##  DeleteListFSA deletes the <n>-th element from list <l>, and closes
##  up. Used for deleting state from an fsa.
##
DeleteListFSA := function(l,n)
    local i, len;
    len := Length(l);
    for i in [n..len] do
      if IsBound(l[i+1]) then
        l[i]:=l[i+1];
      else
        Unbind(l[i]);
      fi;
    od;
end;

#############################################################################
##
#F  DeleteStateFSA(<fsa>) . . . . . . . delete state from an fsa
##  DeleteStateFSA deletes the final state of the fsa <fsa>.
##  All edges to and from that state are deleted.
##  To delete a state other than the final, first call PermuteStatesFSA
##  Public function.
DeleteStateFSA := function ( fsa )
    local  ns, ng, row, i, j;
    if fsa.states.type = "product" then
      Error("Cannot alter a product-type state-list");
    fi;
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    ns := fsa.states.size;
    ng := fsa.alphabet.size;
    fsa.states.size:=ns-1;
    if IsBound(fsa.states.names) then
      Unbind(fsa.states.names[ns]);
    fi;
    if IsBound(fsa.states.setToLabels) then
      Unbind(fsa.states.setToLabels[ns]);
    fi;
    j := Position(fsa.initial,ns);
    if j <> fail then
      DeleteListFSA(fsa.initial,j);
    fi;
    j := Position(fsa.accepting,ns);
    if j <> fail then
      DeleteListFSA(fsa.accepting,j);
    fi;
    if IsBound(fsa.table.defaultTarget) and fsa.table.defaultTarget=ns then
      Unbind(fsa.table.defaultTarget);
    fi;
    if IsBound(fsa.denseDTable) then
      for i in [1..ns-1] do
        row:=fsa.denseDTable[i];
        for j in [1..ng] do
          if row[j]=ns then
            row[j]:=0;
          fi;
        od;
      od;
      DeleteListFSA(fsa.denseDTable,ns);
    fi;
    if IsBound(fsa.sparseTable) then
      for i in [1..ns-1] do
        row:=fsa.sparseTable[i];
        j := 1;
        while j <= Length(row) do
          if row[j][2]=ns then
            DeleteListFSA(row,j);
            j:=j-1;
          fi;
          j:=j+1;
        od;
      od;
      DeleteListFSA(fsa.sparseTable,ns);
    fi;
    Unbind(fsa.backTable);
    RemoveSet(fsa.flags,"NFA");
    RemoveSet(fsa.flags,"BFS");
    RemoveSet(fsa.flags,"minimized");
    RemoveSet(fsa.flags,"trim");
    RemoveSet(fsa.flags,"accessible");
end;

#############################################################################
##
#F  PermuteStatesFSA(<fsa>,p) . . . . . . . permute states of an fsa
##  PermuteStatesFSA permutes the states of the fsa <fsa>.
##  <p> should be a permutation of the state numbers.
##  What was state n is renumbered state n^p.
##  Public function.
PermuteStatesFSA := function ( fsa,p )
    local  ns, term, row, i, j, new, ne;
    if fsa.states.type = "product" then
      Error("Cannot alter a product-type state-list");
    fi;
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    ns := fsa.states.size;
    ne := fsa.alphabet.size;
    if p = () then
      return;
    fi;
    if not IsPerm(p) or LargestMovedPointPerm(p)>ns then
      Error("Second argument is invalid.");
    fi;
    if IsBound(fsa.states.names) then
      new := [];
      for i in [1..ns] do
         new[i^p]:=fsa.states.names[i];
      od;
      fsa.states.names := new;
    fi;
    if IsBound(fsa.states.setToLabels) then
      new := [];
      for i in [1..ns] do
         if IsBound(fsa.states.setToLabels[i]) then
           new[i^p]:=fsa.states.setToLabels[i];
         fi;
      od;
      fsa.states.setToLabels := new;
    fi;
    for i in [1..Length(fsa.initial)] do
       fsa.initial[i]:=fsa.initial[i]^p;
    od;
    fsa.initial := Set(fsa.initial);
    for i in [1..Length(fsa.accepting)] do
       fsa.accepting[i]:=fsa.accepting[i]^p;
    od;
    fsa.accepting := Set(fsa.accepting);
    if IsBound(fsa.table.defaultTarget) and fsa.table.defaultTarget>0 then
      fsa.table.defaultTarget := fsa.table.defaultTarget^p;
    fi;
    if IsBound(fsa.denseDTable) then
      new := [];
      for i in [1..ns] do
        row := fsa.denseDTable[i];
        new[i^p] := row;
        for j in [1..ne] do
          if row[j]>0 then
            row[j] := row[j]^p;
          fi;
        od;
      od;
      fsa.denseDTable := new;
    fi;
    if IsBound(fsa.sparseTable) then
      new := [];
      for i in [1..ns] do
        row := fsa.sparseTable[i];
        new[i^p] := row;
        for term in row do
          if term[2]>0 then
            term[2] := term[2]^p;
          fi;
        od;
      od;
      fsa.sparseTable := new;
    fi;
    if fsa.table.format = "dense deterministic" then
      fsa.table.transitions := fsa.denseDTable;
    else
      fsa.table.transitions := fsa.sparseTable;
    fi;
    Unbind(fsa.backTable);
    RemoveSet(fsa.flags,"BFS");
end;

#############################################################################
##
#F  AddLetterFSA(<fsa>[,<name>]) . . . . . . . adds letter to alphabet of fsa
##  AddLetterFSA adds an extra symbol to the alphabet of the fsa <fsa>.
##  It has the optional name or label <name> (but if the alphabet-type is
##  a named type, then the name must be supplied).
##  Public function.
AddLetterFSA := function ( arg )
    local  fsa, name,  ne, new, term;
    fsa := arg[1];
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if fsa.alphabet.type = "product" then
      Error("Cannot alter a product-type alphabet");
    fi;
    if Length(arg)=1 and IsBound(fsa.alphabet.names) then
       Error("You must supply a name for the new state.");
    fi;
    name := "";
    if Length(arg)=2 then
      name := arg[2];
    fi;
    if not IsInitializedFSA(fsa) then
       Error("First argument is not an initialized fsa.");
    fi;
    fsa.alphabet.size := fsa.alphabet.size+1;
    ne := fsa.alphabet.size;
    if name<>""  and  IsBound(fsa.alphabet.names) then
        fsa.alphabet.names[ne] := name;
    fi;
    if IsBound(fsa.denseDTable) then
      for term in fsa.denseDTable do
        if IsBound(fsa.table.defaultTarget) then
          Add(term,fsa.table.defaultTarget);
        else
          Add(term,0);
        fi;
      od;
    fi;
end;

#############################################################################
##
#F  DeleteLetterFSA(<fsa>) . . . . . . . deletes alphabet letter from an fsa
##  DeleteLetterFSA deletes the final alphabet label from the fsa <fsa>.
##  All edges with that label are deleted.
##  To delete an edge-label other than the final, first call
##  PermuteLettersFSA
##  Public function.
DeleteLetterFSA := function ( fsa )
    local  ns, ne, term, row, i, j;
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if fsa.alphabet.type = "product" then
      Error("Cannot alter a product-type alphabet");
    fi;
    ns := fsa.states.size;
    ne := fsa.alphabet.size;
    fsa.alphabet.size := ne-1;
    if IsBound(fsa.alphabet.names) then
      Unbind(fsa.alphabet.names[ne]);
    fi;
    if IsBound(fsa.alphabet.setToLabels) then
      Unbind(fsa.alphabet.setToLabels[ne]);
    fi;
    RemoveSet(fsa.flags,"BFS");
    RemoveSet(fsa.flags,"minimized");
    if IsBound(fsa.denseDTable) then
      for row in fsa.denseDTable do
        DeleteListFSA(row,ne);
      od;
    fi;
    if IsBound(fsa.sparseTable) then
      for row in fsa.sparseTable do
        j := 1;
        while j <= Length(row) do
          if row[j][1]=ne then
            DeleteListFSA(row,j);
          fi;
          j:=j+1;
        od;
      od;
    fi;
    Unbind(fsa.backTable);
    RemoveSet(fsa.flags,"NFA");
    RemoveSet(fsa.flags,"BFS");
    RemoveSet(fsa.flags,"minimized");
    RemoveSet(fsa.flags,"trim");
    RemoveSet(fsa.flags,"accessible");
end;

#############################################################################
##
#F  PermuteLettersFSA(<fsa>,p) . . . . . . . permute alphabet labels of an fsa
##  PermuteLettersFSA permutes the alphabet labels of the fsa <fsa>.
##  <p> should be a permutation of the alphabet labels numbers.
##  What was edge-label n is renumbered alphabet label n^p.
##  Public function.
PermuteLettersFSA := function ( fsa,p )
    local  ns, ne, term, row, i, j, new;
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if fsa.alphabet.type = "product" then
      Error("Cannot alter a product-type alphabet");
    fi;
    ns := fsa.states.size;
    ne := fsa.alphabet.size;
    if not IsPerm(p) or LargestMovedPointPerm(p)>ne then
      Error("Second argument is invalid.");
    fi;
    if IsBound(fsa.alphabet.names) then
      new := [];
      for i in [1..ne] do
        new[i^p]:=fsa.alphabet.names[i];
      od;
      fsa.alphabet.names := new;
    fi;
    if IsBound(fsa.alphabet.setToLabels) then
      new := [];
      for i in [1..ne] do
         if IsBound(fsa.alphabet.setToLabels[i]) then
           new[i^p]:=fsa.alphabet.setToLabels[i];
         fi;
      od;
      fsa.alphabet.setToLabels := new;
    fi;
    if IsBound(fsa.denseDTable) then
      for i in [1..ns] do
        row := fsa.denseDTable[i];
        new := [];
        for j in [1..ne] do
          new[j^p] := row[j];
        od;
        fsa.denseDTable[i] := new;
      od;
    fi;
    if IsBound(fsa.sparseTable) then
      new := [];
      for i in [1..ns] do
        row := fsa.sparseTable[i];
        for term in row do
          if term[1]>0 then
            term[1] := term[1]^p;
          fi;
        od;
      od;
    fi;
    if fsa.table.format = "dense deterministic" then
      fsa.table.transitions := fsa.denseDTable;
    else
      fsa.table.transitions := fsa.sparseTable;
    fi;
    Unbind(fsa.backTable);
    RemoveSet(fsa.flags,"BFS");
end;

#############################################################################
#F  AddEdgeFSA(<fsa>,<e>,<s>,<t>) . . . . . . . adds edge to an fsa
##  AddEdge adds an edge with source <s>, label <e> and target <t>
##  to the fsa <fsa> (if there isn't one already. 
##  <s> and <t> can be either numbers or names of states,
##  and <e> a number or name of an edge-label.
##  Public function.
AddEdgeFSA := function ( fsa, e, s, t )
    local row, term, ng;
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if IsList(e) then
      ng := fsa.alphabet.base.size;
      e := (ElementNumberSR(fsa.alphabet,e[1])-1) * (ng+1) + 
       ElementNumberSR(fsa.alphabet,e[2]);
    else 
      e := ElementNumberSR(fsa.alphabet,e);
    fi;
    if e=false then
      Error("Second argument is not a valid edge number or label.");
    fi;
    s := ElementNumberSR(fsa.states,s);
    if s=false then
       Error("Third argument is not a valid state number or name.");
    fi;
    t := ElementNumberSR(fsa.states,t);
    if t=false then
       Error("Fourth argument is not a valid state number or name.");
    fi;
    if e=0 or (IsBound(fsa.denseDTable) and fsa.denseDTable[s][e]>0 and
       fsa.denseDTable[s][e]<=fsa.states.size and
       fsa.denseDTable[s][e] <> t) then
    # makes non-deterministic.
      Print("Warning: gone non-deterministic!\n");
      SparseTableFSA(fsa);
      fsa.table.format := "sparse";
      fsa.table.transitions := fsa.sparseTable;
      Unbind(fsa.denseDTable);
      RemoveSet(fsa.flags,"DFA");
      AddSet(fsa.flags,"NFA");
    fi;
    if IsBound(fsa.denseDTable) then
      fsa.denseDTable[s][e] := t;
    fi;
    if IsBound(fsa.sparseTable) then
      row := fsa.sparseTable[s];
      for term in row do
        if term[1]=e and term[2]>0 and term[2]<=fsa.states.size
            and term[2] <> t then
          #makes non-deterministic
          RemoveSet(fsa.flags,"DFA");
          AddSet(fsa.flags,"NFA");
          fsa.table.format := "sparse";
        fi;
      od;
      Add(row,[e,t]);
      fsa.sparseTable[s]:=Set(row);
    fi;
    Unbind(fsa.backTable);
    RemoveSet(fsa.flags,"BFS");
    RemoveSet(fsa.flags,"minimized");
end;

#############################################################################
##
#F  DeleteEdgeFSA(<fsa>,<e>,<s>,<t>) . . . . . . . deletes edge from an fsa
##  DeleteEdgeFSA deletes an edge with source <s>, label <e> and target <t>
##  from the fsa <fsa> (if there is one). 
##  <s> and <t> can be either numbers or names of states (but both the same),
##  and <e> a number or name of an edge-label.
##  Public function.
DeleteEdgeFSA := function ( fsa, e, s, t )
    local ng, row, term, subterm,  j, dfa_check;
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if IsList(e) then
      ng := fsa.alphabet.base.size;
      e := (ElementNumberSR(fsa.alphabet,e[1])-1) * (ng+1) + 
       ElementNumberSR(fsa.alphabet,e[2]);
    else 
      e := ElementNumberSR(fsa.alphabet,e);
    fi;
    if e=false then
      Error("Second argument is not a valid edge number or label.");
    fi;
    s := ElementNumberSR(fsa.states,s);
    if s=false then
       Error("Third argument is not a valid state number or name.");
    fi;
    t := ElementNumberSR(fsa.states,t);
    if t=false then
       Error("Fourth argument is not a valid state number or name.");
    fi;
    if IsBound(fsa.denseDTable) and fsa.denseDTable[s][e] = t then
      fsa.denseDTable[s][e]:=0;
    fi;
    if IsBound(fsa.sparseTable) then
      row := fsa.sparseTable[s];
      j := 1;
      while j <= Length(row) do
        term := row[j];
        if term[1]=e and term[2] = t then
          DeleteListFSA(row,j);
        fi;
        j := j+1;
      od;
    fi;
    Unbind(fsa.backTable);
    RemoveSet(fsa.flags,"BFS");
    RemoveSet(fsa.flags,"minimized");
    RemoveSet(fsa.flags,"NFA");
    # may have gone deterministic.
    RemoveSet(fsa.flags,"accessible");
    RemoveSet(fsa.flags,"trim");
end;

#############################################################################
##
#F  AcceptingStatesFSA(<fsa>) . . . the accepting states of <fsa>
##
AcceptingStatesFSA := function(fsa)
  return fsa.accepting;
end;

#############################################################################
##
#F  SetAcceptingFSA(<fsa>, <s>, <flag>) . . . set category of state <s>
##
##  s should be a number or name of a state in fsa <fsa>. This state
##  is made into an accepting state or not according to whether
##  <flag> is true or false.
##
##  Public function
SetAcceptingFSA := function(fsa, s, flag)
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    s := ElementNumberSR(fsa.states,s);
    if s=false then
       Error("Second argument is not a valid state number or name.");
    fi;
    if flag = true then
      AddSet(fsa.accepting,s);
    else
      RemoveSet(fsa.accepting,s);
    fi;
    RemoveSet(fsa.flags,"trim");
    RemoveSet(fsa.flags,"minimized");
end;

#############################################################################
##
#F  InitialStatesFSA(<fsa>) . . . the initial states of <fsa>
##
InitialStatesFSA := function(fsa)
  return fsa.initial;
end;

#############################################################################
##
#F  SetInitialFSA(<fsa>, <s>, <flag>) . . . set initiality of state <s>
##
##  s should be a number or name of a state in fsa <fsa>. This state
##  is made into an initial state or not according to whether
##  <flag> is true or false.
##
##  Public function
SetInitialFSA := function(fsa, s, flag)
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    s := ElementNumberSR(fsa.states,s);
    if s=false then
       Error("Second argument is not a valid state number or name.");
    fi;
    if flag = true then
      AddSet(fsa.initial,s);
    else
      RemoveSet(fsa.initial,s);
    fi;
    RemoveSet(fsa.flags,"trim");
    RemoveSet(fsa.flags,"accessible");
    RemoveSet(fsa.flags,"BFS");
    RemoveSet(fsa.flags,"minimized");
    if Length(fsa.initial) > 1 then
      RemoveSet(fsa.flags,"DFA");
    else
      RemoveSet(fsa.flags,"NFA");
    fi;
end;

#############################################################################
##
#F  IsAccessibleFSA(<fsa>) . . . . . . . test whether fsa is a accessible fsa
##
## An accessible FSA is one in which there is a word in the language
## leading to every state.
## The string "accessible" is inserted in the list of flags when it is known
## to be accessible.
## Note that "trim" implies "accessible".
##
## Public function.
IsAccessibleFSA := function ( fsa )
    local ns, ne, ct, i, j, got, s, x, t;
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if "accessible" in fsa.flags or "trim" in fsa.flags then
      return true;
    fi;
    ns := fsa.states.size;
    ne := fsa.alphabet.size;
 # Find all accessible states i.e. states accessible from an initial state.
    got := ShallowCopy(fsa.initial);
    ct := Length(got);
    i := 1;
    while i <= ct do
      s := got[i];
      for j in [0..ne] do
        x := TargetsFSA(fsa,j,s);
        for t in x do
          if t>0 and not t in got then
            ct := ct+1;
            got[ct] := t;
          fi;
        od;
      od;
      i := i+1;
    od;
    if ct <> ns then
 # there are some inaccessible states, so fsa is not accessible.
      return false;
    fi;

    AddSet(fsa.flags,"accessible");
    return true;
end;

#############################################################################
##
#F  AccessibleFSA(<fsa>) . . . . . . . replace fsa by an accessible fsa
##
## AccessibleFSA(<fsa>) removes non-accessible from
## <fsa> to make it accessible, without changing the accepted language.
## An accessible FSA is one in which there is a word in the language
## leading to every state.
## The string "accessible" is inserted in the list of flags when it is known
## to be accessible.
##
## Public function.
AccessibleFSA := function ( fsa )
    local ns, ne, ct, i, j, got, s, x, t;
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if "accessible" in fsa.flags or "trim" in fsa.flags then
      return;
    fi;
    ns := fsa.states.size;
    ne := fsa.alphabet.size;
 # Find all accessible states i.e. states accessible from an initial state.
    got := ShallowCopy(fsa.initial);
    ct := Length(got);
    i := 1;
    while i <= ct do
      s := got[i];
      for j in [0..ne] do
        x := TargetsFSA(fsa,j,s);
        for t in x do
          if t>0 and not t in got then
            ct := ct+1;
            got[ct] := t;
          fi;
        od;
      od;
      i := i+1;
    od;
    if ct <> ns then
 # there are some inaccessible states, so remove them - because we can only
 # remove the last state, we have to work from the back.
      for s in Reversed([1..ns]) do
        if not s in got then
          if s<ns then
            PermuteStatesFSA(fsa,(s,ns));
          fi;
          DeleteStateFSA(fsa);
          ns := ns-1;
        fi;
      od;
    fi;
      
    AddSet(fsa.flags,"accessible");
end;
 
#############################################################################
##
#F  IsTrimFSA(<fsa>) . . . . . . . test whether fsa is a trim fsa
##
## A trim FSA is one in which there is an accepted word in the language
## through every state.
## The string "trim" is inserted in the list of flags when it is known
## to be trim.
##
## Public function.
IsTrimFSA := function ( fsa )
    local ns, ne, ct, i, j, got, s, x, t;
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if "trim" in fsa.flags  then
      return true;
    fi;
    ns := fsa.states.size;
    ne := fsa.alphabet.size;
 # First find all accessible states
 # i.e. states accessible from an initial state.
    got := ShallowCopy(fsa.initial);
    ct := Length(got);
    i := 1;
    while i <= ct do
      s := got[i];
      for j in [0..ne] do
        x := TargetsFSA(fsa,j,s);
        for t in x do
          if t>0 and not t in got then
            ct := ct+1;
            got[ct] := t;
          fi;
        od;
      od;
      i := i+1;
    od;
    if ct <> ns then
 # there are some inaccessible states, so fsa is not trim.
      return false;
    fi;
      
 # Next find all co-accessible states
 # i.e. states from which a path starts to an accepting state
    got := ShallowCopy(fsa.accepting);
    ct := Length(got);
    i := 1;
    while i <= ct do
      s := got[i];
      for j in [0..ne] do
        x := SourcesFSA(fsa,j,s);
        for t in x do
          if not t in got then
            ct := ct+1;
            got[ct] := t;
          fi;
        od;
      od;
      i := i+1;
    od;
    if ct <> ns then
 # there are some non co-accessible states, so fsa is not trim.
      return false;
    fi;
    AddSet(fsa.flags,"trim");
    return true;
end;

#############################################################################
##
#F  TrimFSA(<fsa>) . . . . . . . replace fsa by a trim fsa
##
## TrimFSA(<fsa>) removes non-accessible and non-coaccessible states from
## <fsa> to make it trim, without changing the accepted language.
## A trim FSA is one in which there is an accepted word in the language
## through every state.
## The string "trim" is inserted in the list of flags when it is known
## to be trim.
## (Removing the non-coaccessible states cannot possibly make any other
##  states non-accessible, so there is no need to repeat the process.)
##
## Public function.
TrimFSA := function ( fsa )
    local ns, ne, ct, i, j, got, s, x, t;
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if "trim" in fsa.flags  then
      return;
    fi;
    ns := fsa.states.size;
    ne := fsa.alphabet.size;
 # First find all accessible states
 # i.e. states accessible from an initial state.
    got := ShallowCopy(fsa.initial);
    ct := Length(got);
    i := 1;
    while i <= ct do
      s := got[i];
      for j in [0..ne] do
        x := TargetsFSA(fsa,j,s);
        for t in x do
          if t>0 and not t in got then
            ct := ct+1;
            got[ct] := t;
          fi;
        od;
      od;
      i := i+1;
    od;
    if ct <> ns then
 # there are some inaccessible states, so remove them - because we can only
 # remove the last state, we have to work from the back.
      for s in Reversed([1..ns]) do
        if not s in got then
          if s<ns then
            PermuteStatesFSA(fsa,(s,ns));
          fi;
          DeleteStateFSA(fsa);
          ns := ns-1;
        fi;
      od;
    fi;
      
 # Next find all co-accessible states
 # i.e. states from which a path starts to an accepting state
    got := ShallowCopy(fsa.accepting);
    ct := Length(got);
    i := 1;
    while i <= ct do
      s := got[i];
      for j in [0..ne] do
        x := SourcesFSA(fsa,j,s);
        for t in x do
          if not t in got then
            ct := ct+1;
            got[ct] := t;
          fi;
        od;
      od;
      i := i+1;
    od;
    if ct <> ns then
 # there are some non-coaccessible states, so remove them - because we can only
 # remove the last state, we have to work from the back.
      for s in Reversed([1..ns]) do
        if not s in got then
          if s<ns then
            PermuteStatesFSA(fsa,(s,ns));
          fi;
          DeleteStateFSA(fsa);
          ns := ns-1;
        fi;
      od;
    fi;
    AddSet(fsa.flags,"trim");
    RemoveSet(fsa.flags,"accessible"); #trim implies accessible
    RemoveSet(fsa.flags,"BFS");
end;
 
#############################################################################
##
#F  IsBFSFSA(<fsa>) . . . . . . . decide if fsa has the "bfs" property
##
## IsBFSFSA(<fsa>) decides if the fsa <fsa> has the breadth-first-search
## property. This means that it is accessible and, scanning the transition table
## along the states, one encounters the states in ascending numerical order.
## It is useful for comparing two fsa's.
##
## Public function.
IsBFSFSA := function ( fsa )
    local ns, ne, ct, i, j, got, s, x, t;
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if "BFS" in fsa.flags  then
      return true;
    fi;
    if not IsAccessibleFSA(fsa) then
      return false;
    fi;
    ns := fsa.states.size;
    ne := fsa.alphabet.size;
    if fsa.initial <> [1..Length(fsa.initial)] then
      return false;
    fi;
    ct := Length(fsa.initial);
    i := 1;
    while i <= ct do
      for j in [0..ne] do
        x := TargetsFSA(fsa,j,i);
        for t in x do
          if t>ct then
            if t <> ct+1 then
              return false;
            fi;
            ct := ct+1;
            if ct = ns then
              AddSet(fsa.flags,"BFS");
              return true;
            fi;
          fi;
        od;
      od;
      i := i+1;
    od;

end;

#############################################################################
##
#F  BFSFSA(<fsa>) . . . . . . . replace fsa by an fsa with the "bfs" property
##
## BFSFSA(<fsa>) replaces the fsa <fsa> by one with the same language
## that has the breadth-first-search property. This means that, scanning
## the transition table along the states, one encounters the states
## in ascending numerical order. It is useful for comparing two fsa's.
## It first makes the fsa trim, and then calculates the required
## state-permutation to achieve bfs-form, and calls PermuteStatesFSA.
##
## Public function.
BFSFSA := function ( fsa )
    local ns, ne, ct, perm, i, j, got, s, x, t;
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if "BFS" in fsa.flags  then
      return;
    fi;
    AccessibleFSA(fsa);
    ns := fsa.states.size;
    ne := fsa.alphabet.size;
 # We calculate the required permutation by building up the list perm
 # perm[i]=j means that the i-th state in the new order will be the
 # current j-th state - so we will call PermuteStatesFSA with the
 # inverse of perm.
    perm := ShallowCopy(fsa.initial);
    ct := Length(perm);
    i := 1;
    while i <= ct do
      s := perm[i];
      for j in [0..ne] do
        x := TargetsFSA(fsa,j,s);
        for t in x do
          if t>0 and not t in perm then
            ct := ct+1;
            perm[ct] := t;
          fi;
        od;
      od;
      i := i+1;
    od;

    perm := PermList(perm)^-1;
    PermuteStatesFSA(fsa,perm);
    AddSet(fsa.flags,"BFS");
end;

#############################################################################
##
#F  PSizeFSA(<fsa>,[<state-list>]) . . . . . number of accepted paths of an fsa
##
##  <fsa> should be a finite state automaton.
##  The number of accepted paths is calculated and returned.
##  WARNING: if there are epsilon transitions, then this is not necessarily
##  the same as the size of the accepted language.
##  If this is infinite, "infinity" is returned.
##  If <fsa. is not trim, then a diagnostic will be printed.
##  
##  If the optional argument [<state-list>] is present, then the number
##  of accepted strings starting at one of the states in <state-list> will
##  be returned instead, BUT ONLY IF THE TOTAL ACCEPTED LANGUAGE IS FINITE.
##  Public function.
PSizeFSA := function ( arg )
    local fsa, slist, ns, ne, indeg, st, olist, nacc, total, ct, i, j, s, t, x;
    fsa := arg[1];
    if Length(arg)=2 then
      slist := arg[2];
    else
      slist := fsa.initial;
    fi;
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if not IsTrimFSA(fsa) then
      Print("#The fsa is not trim. Call TrimFSA(fsa) to make it trim.\n");
      return "unknown";
    fi;

    ns := fsa.states.size;
    if ns=0 then
      return 0;
    fi;
    ne := fsa.alphabet.size;

 # We first count the number of edges going into each vertex.
    indeg := [];
    for s in [1..ns] do
      indeg[s] := 0;
    od;
    for s in [1..ns] do
      for i in [0..ne] do
        x := TargetsFSA(fsa,i,s);
        for t in x do
          if t > 0 then indeg[t] := indeg[t]+1; fi;
        od;
      od;
    od;

 # Now we seek to order the states so that if state s <= state t, then there
 # is no path from state t to state s. If this is not possible, then the
 # accepted language must be infinite.
 # The ordering will be in the list olist.

    st := 0;
    for s in fsa.initial do 
      if indeg[s]=0 then
        st := s;
      fi;
    od;
    if st = 0 then
      return infinity;
    fi;
    olist := [st];
    ct := 1;
    i := 1;
    while i<=ct do
      s := olist[i];
      for j in [0..ne] do
        x := TargetsFSA(fsa,j,s);
        for t in x do
          if t>0 then
            indeg[t] := indeg[t]-1;
            if indeg[t]=0 then
              ct := ct+1;
              olist[ct] := t;
            fi;
          fi;
        od;
      od;
      i := i+1;
    od;
    if ct <> ns then
      return infinity;
    fi;

 # We have built the list, so the accepted language is finite. Now we work
 # backwards through the list, calculating the number of accepted words
 # starting at that state.
 # We store the numbers in nacc.
 
  indeg := 0; #no longer needed.
  nacc := [];
  for i in Reversed([1..ns]) do
    s := olist[i];
    nacc[s] := 0;
    for j in [0..ne] do
      x := TargetsFSA(fsa,j,s);
      for t in x do
        if t>0 then nacc[s] := nacc[s]+nacc[t]; fi;
      od;
    od;
    if s in fsa.accepting then
      nacc[s] := nacc[s]+1;
    fi;
  od;

 # Finally we count the total number of accepted strings starting from
 # one of the states in slist.
  total := 0;
  for s in slist do
    total := total+nacc[s];
  od;
  return total;
end;

#############################################################################
##
#F  LSizeDFA(<fsa>,[<initial state>]) . . . . . size of language of an fsa
##
##  <fsa> should be a deterministic finite state automaton.
##  The size of the accepted language is calculated.
##  This should be quicker than PSizeFSA for deterministic automata.
##  If the language is infinite, "infinity" is returned.
##  If <fsa> is not trim, then a diagnostic will be printed.
##  
##  If the optional argument [<initial state>] is present, then the number
##  of accepted strings starting at the state in <initial state> will
##  be returned instead.
##  
##  Public function.
LSizeDFA := function ( arg )
    local fsa, slist, ns, ne, ttable, indeg, st, olist, nacc, total, ct,
          i, j, s, t, accstates;
    fsa := arg[1];
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if IsDeterministicFSA(fsa)=false  then
       Error("First argument is not a dfa.");
    fi;
    if not IsTrimFSA(fsa) then
      Print("#The fsa is not trim. Call TrimFSA(fsa) to make it trim.\n");
      return "unknown";
    fi;

    ns := fsa.states.size;
    if ns=0 then
      return 0;
    fi;
    ne := fsa.alphabet.size;

 # First make sure that the dense deterministic table is present.
    DenseDTableFSA(fsa);
    ttable := fsa.denseDTable;

    if Length(arg)=2 then
      slist := [arg[2]];
      #In this case, we restrict attention to states that can be reached from
      #initial states.
      accstates := ShallowCopy(slist);
      ct := 1;
      i := 1;
      while i<=ct do
        s := accstates[i];
        for j in [1..ne] do
          t := ttable[s][j];
          if t > 0 and Position(accstates,t) = fail then
            ct := ct+1;
            Add(accstates,t);
          fi;
        od;
        i := i+1;
      od;
    else
      slist := fsa.initial;
      accstates := [1..ns];
    fi;

 # We first count the number of edges going into each vertex.
    indeg := [];
    for s in accstates do
      indeg[s] := 0;
    od;
    for s in accstates do
      for i in [1..ne] do
        t := ttable[s][i];
        if t > 0 then indeg[t] := indeg[t]+1; fi;
      od;
    od;

 # Now we seek to order the states so that if state s <= state t, then there
 # is no path from state t to state s. If this is not possible, then the
 # accepted language must be infinite.
 # The ordering will be in the list olist.

    ns := Length(accstates);
    st := slist[1];
    if indeg[st] <> 0 then
      return infinity;
    fi;
    olist := [st];
    ct := 1;
    i := 1;
    while i<=ct do
      s := olist[i];
      for j in [1..ne] do
        t := ttable[s][j];
        if t>0 then
            indeg[t] := indeg[t]-1;
            if indeg[t]=0 then
              ct := ct+1;
              olist[ct] := t;
            fi;
        fi;
      od;
      i := i+1;
    od;
    if ct <> ns then
      return infinity;
    fi;

 # We have built the list, so the accepted language is finite. Now we work
 # backwards through the list, calculating the number of accepted words
 # starting at that state.
 # We store the numbers in nacc.
 
  indeg := 0; #no longer needed.
  nacc := [];
  for i in Reversed([1..ns]) do
    s := olist[i];
    nacc[s] := 0;
    for j in [1..ne] do
      t := ttable[s][j];
      if t>0 then nacc[s] := nacc[s]+nacc[t]; fi;
    od;
    if s in fsa.accepting then
      nacc[s] := nacc[s]+1;
    fi;
  od;

 # Finally we count the total number of accepted strings starting from
 # one of the states in slist.
  total := 0;
  for s in slist do
    total := total+nacc[s];
  od;
  return total;
end;

#############################################################################
##
#F  ListWordSR(<sr>,<w>) . . . . converts word in sr-generators to list
##
##  ListWordSR converts the word <w> in the generators of the
##  set-record <sr> to a list of integers.
##  It only works if <sr> has type "identifiers" or "product".
##  In the latter case, w should be a list of n words, where n is the
##  "arity" of the set-record.
##
##  Public function.
ListWordSR := function ( sr, w )
    local i, j, l, n, wl, gens, prod, nv, tup, id;
    if not IsRecord(sr) or not IsBound(sr.type) or
           (sr.type <> "identifiers" and sr.type <> "product") then
       Error("First argument must be a set-record of type \"identifiers\".");
    fi;
    prod := sr.type="product";
 #We deal with product type separately.
    if prod then
      nv := sr.arity;
      if not IsList(w) or Length(w)<>nv then
         Error("Second argument must be a list of length sr.arity.");
      fi;
      l := 0;
      for i in w do
        if not IsWord(i) then
           Error("An entry in second argument is not a word.");
        fi;
        if Length(i)>l then
          l := Length(i);
        fi;
      od;
      wl := [];
      gens := sr.names;
      for i in [1..l] do
        tup := [];
        for j in [1..nv] do
          if i > Length(w[j]) then
            id := sr.padding;
          else
            id := Subword(w[j],i,i);
          fi;
          tup[j] := id;
        od;
        n := Position(gens,tup);
        if n=fail then
          Error("Invalid tuple in word.");
        fi;
        Add(wl,n);
      od;
    else
      if not IsWord(w) then
         Error("Second argument is not a word.");
      fi;
      l := Length(w);
      wl := [];
      gens := sr.names;
      for i in [1..l] do
        n := Position(gens,Subword(w,i,i));
        if n=fail then
          Error("Invalid generator in word.");
        fi;
        Add(wl,n);
      od;
    fi;

    return wl;
end;

#############################################################################
##
#F  WordListSR(<sr>,<wl>) . . . . converts list of sr-generators to word
##
##  WordListSR converts the list of positive integers <wl> to a word
##  in the generators of the rewriting system <sr>. Each integer in the
##  list must be a valid generator number.
##  This is the inverse function to ListWordSR.
##  However, it works when sr has type "identifiers", "strings" or
##  "products".
##
##  Public function.
WordListSR := function ( sr, wl )
    local i, j, l, w, gens, ng, nv, tup, IdWord;
    if sr.type="identifiers"   and IsAssocWordWithOne(sr.names[1]) then
      IdWord := sr.names[1]^0;
    elif sr.type="words"   and IsAssocWordWithOne(sr.alphabet[1]) then
      IdWord := sr.alphabet[1]^0;
    else IdWord:=false;
    fi;
    if not IsRecord(sr) or not IsBound(sr.type) or (sr.type <> "identifiers" 
        and sr.type <> "words"  and sr.type <> "strings" and
        sr.type <> "product") then
       Error("First argument must be a set-record of appropriate type.");
    fi;
    if not IsList(wl) then
       Error("Second argument is not a list.");
    fi;
    l := Length(wl);
    gens := sr.names;
    ng := sr.size;
    if l=0 then
      if sr.type="identifiers" or sr.type="words" then
        return IdWord;
      elif sr.type="strings" then
        return "";
      else
        nv := sr.arity;
        return List([1..nv],i->IdWord);
      fi;
    else
      if not wl[1] in [1..ng] then
        Error("List element is not a valid generator number.");
      fi;
      w := ShallowCopy(gens[wl[1]]);
    fi;
    for i in [2..l] do
      if not wl[i] in [1..ng] then
        Error("List element is not a valid generator number.");
      fi;
      if sr.type="identifiers" or sr.type="words" then
        w := w*gens[wl[i]];
      elif sr.type="strings" then
        w := Concatenation(w,gens[wl[i]]);
      else
        tup := gens[wl[i]];
        nv := sr.arity;
        for j in [1..nv] do
          w[j] := w[j]*tup[j];
        od;
      fi;
    od;

    return w;
end;

#############################################################################
##
#F  LEnumerateDFA(<fsa>, <min>, <max>, [<is>] ) . . enumerate language of dfa
##
##  <fsa> should be a deterministic finite state automaton.
##  All words in the language accepted by <fsa> having length l
##  satisfying <min> <= l <= <max> will be calculated and output in a
##  list. These will be in lexacographical order.
##  To get shortlex order, call SortLEnumerateDFA, which merely calls this
##  function repeatedly.
##  If the optional argument <is> is present, the initial state will be
##  taken to be is.
##
##  Public function.
LEnumerateDFA := function ( arg )
    local fsa, min, max, is,  words, convert, ttable, sr, ne, as, cword,
          cstatelist, clength, done, backtrack, cstate, fe, i;

    if Length(arg) < 3 then
       Error("LEnumerateDFA must have at least three arguments");
    fi;
    fsa:=arg[1]; min:=arg[2]; max:=arg[3];
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if  IsDeterministicFSA(fsa)=false  then
       Error("First argument is not a dfa.");
    fi;
    if not IsInt(min) or not IsInt(max) or min<0 or min>max then
      Error("2nd and 3rd arguments must be nonneg. integers with 2nd <= 3rd.");
    fi;
    if fsa.initial=[] and Length(arg)=3 then
      return [];
    fi;
    if Length(arg)>=4 then is:=arg[4]; else is:=fsa.initial[1]; fi;

 # The enumeration process itself will use lists of integers. These will be
 # converted to words if necessary and collected in the lists "words" for
 # output.

    sr := fsa.alphabet;
    ne := sr.size;
    convert := sr.type="identifiers" or sr.type="strings" or sr.type="words"
                or sr.type="product";

  # Make sure that the dense deterministic table is present.
    DenseDTableFSA(fsa);
    ttable := fsa.denseDTable;

    words := [];
  # cword will be the current word in the search (as a list of integers),
  # clength its current length, and cstatelist the list of states of fsa
  # arising when scanning the word.
    cword := [];
    cstatelist := [is];
    clength := 0;

    as := fsa.accepting;
  # Now the backtrack search begins
    done := false;
    while not done do
  # first check if we want the current word.
      if clength>=min and cstatelist[clength+1] in as then
         if convert then
           Add(words,WordListSR(sr,cword));
         else
           Add(words,ShallowCopy(cword));
         fi;
      fi;

  # now proceed to next word in search.
      fe := 1;
      backtrack:=true;
      while backtrack and not done  do
        if clength < max then
          cstate := cstatelist[clength+1];
          i := fe;
          while backtrack and i<= ne do
            if ttable[cstate][i] > 0 then
           # found next node
              clength := clength+1;
              cword[clength] := i;
              cstatelist[clength+1] := ttable[cstate][i];
              backtrack := false;
            fi;
            i := i+1;
          od;
        fi;
        if backtrack then
           if clength=0 then
             done := true;
           else
             fe := cword[clength]+1;
             Unbind(cword[clength]);
             clength := clength-1;
           fi;
        fi;
      od;
    od;

    return words;
end;

#############################################################################
##
#F  SortLEnumerateDFA(<fsa>, <min>, <max> [,<is>])
##  . . . . . . . . . . . . . . . . . . . enumerate language of dfa and sort
##
##  This function merely calls LEnumerateFSA repeatedly to get the shortlex
##  order of output.
##
##  If the optional argument <is> is present, the initial state will be
##  taken to be is.
##
##  Public function.
SortLEnumerateDFA := function ( arg )
    local fsa, min, max, is,  words, i;

    if Length(arg) < 3 then
       Error("SortLEnumerateDFA must have at least three arguments");
    fi;
    fsa:=arg[1]; min:=arg[2]; max:=arg[3];

    words := [];
    for i in [min..max] do
      if Length(arg)=3 then
        words := Concatenation(words,LEnumerateDFA(fsa,i,i));
      else
        is := arg[4];
        words := Concatenation(words,LEnumerateDFA(fsa,i,i,is));
      fi;
    od;

    return words;
end;

#############################################################################
##
#F  SizeLEnumerateDFA(<fsa>, <min>, <max> [,<is>])
##  . . . . . . . . . . . . . . . . . . . size of enumerated language of dfa
##
##  <fsa> should be a deterministic finite state automaton.
##  This is like LEnumerateFSA, but only the number of accepted words is
##  output.
##
##  If the optional argument <is> is present, the initial state will be
##  taken to be is.
##
##  Public function.
SizeLEnumerateDFA := function ( arg )
    local fsa, min, max, is, nwords, ttable, sr, ne, as, cword, cstatelist,
          clength, done, backtrack, cstate, fe, i;

    if Length(arg) < 3 then
       Error("LEnumerateDFA must have at least three arguments");
    fi;
    fsa:=arg[1]; min:=arg[2]; max:=arg[3];

    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if IsDeterministicFSA(fsa)=false  then
       Error("First argument is not a dfa.");
    fi;
    if not IsInt(min) or not IsInt(max) or min<0 or min>max then
      Error("2nd and 3rd arguments must be nonneg. integers with 2nd <= 3rd.");
    fi;
    if fsa.initial=[] and Length(arg)=3 then
      return 0;
    fi;

    if Length(arg)>=4 then is:=arg[4]; else is:=fsa.initial[1]; fi;

  # The enumeration process itself will use lists of integers.

    sr := fsa.alphabet;
    ne := sr.size;

  # Make sure that the dense deterministic table is present.
    DenseDTableFSA(fsa);
    ttable := fsa.denseDTable;

    nwords := 0;
  # cword will be the current word in the search (as a list of integers),
  # clength its current length, and cstatelist the list of states of fsa
  # arising when scanning the word.
    cword := [];
    cstatelist := [is];
    clength := 0;

    as := fsa.accepting;
  # Now the backtrack search begins
    done := false;
    while not done do
  # first check if we want the current word.
      if clength>=min and cstatelist[clength+1] in as then
        nwords := nwords+1;
      fi;

  # now proceed to next word in search.
      fe := 1;
      backtrack:=true;
      while backtrack and not done  do
        if clength < max then
          cstate := cstatelist[clength+1];
          i := fe;
          while backtrack and i<= ne do
            if ttable[cstate][i] > 0 then
           # found next node
              clength := clength+1;
              cword[clength] := i;
              cstatelist[clength+1] := ttable[cstate][i];
              backtrack := false;
            fi;
            i := i+1;
          od;
        fi;
        if backtrack then
           if clength=0 then
             done := true;
           else
             fe := cword[clength]+1;
             Unbind(cword[clength]);
             clength := clength-1;
           fi;
        fi;
      od;
    od;

    return nwords;
end;

#############################################################################
##
#F  SubstitutedListFSA(<l>,<pos1>,<pos2>,<ss>)
##                        . . . . . . . . . substitute a new list in a list
##
##  The part of the list <l> form position <pos1> to <pos2> is substituted by
##  the list <ss>. This is easy if lengths are equal. Otherwise not so.
##
##  Private function.
SubstitutedListFSA := function(l,pos1,pos2,ss)
    local len, oldlen, newlen, diff, i;
    len := Length(l);
    oldlen := pos2-pos1+1; newlen := Length(ss);
    if oldlen=newlen then
      l{[pos1..pos2]} := ss;
    elif newlen<oldlen then
      diff := oldlen-newlen;
      for i in [pos2+1..len] do l[i-diff]:=l[i]; od;
      for i in [len-diff+1..len] do Unbind(l[i]); od;
      l{[pos1..pos2-diff]} := ss;
    elif newlen>oldlen then
      diff := newlen-oldlen;
      for i in Reversed([pos2+1..len]) do l[i+diff] := l[i]; od;
      l{[pos1..pos2+diff]} := ss;
    fi;
end;

#############################################################################
##
#F  DeterminizeFSA(<fsa>) . . . call external program to determinize fsa <fsa>
##
## Determinized FSA is returned.
## Public function.
DeterminizeFSA := function(fsa)
  local callstring, filename, alph;
    
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if  IsDeterministicFSA(fsa)  then
       return  fsa;
    fi;
    ## We replace the alphabet by simple-type alphabet for the
    ## I/O phase.
    alph := fsa.alphabet;
    fsa.alphabet := rec(type:="simple",size:=alph.size);
    InitializeSR(fsa.alphabet);
    filename := Concatenation(_KBTmpFileName,".fsafordet");
    WriteFSA(fsa,"_FSA",filename,";");
    callstring := Filename(_KBExtDir,"nfadeterminize");
    if InfoLevel(InfoFSA)=0 then
       callstring := Concatenation(callstring," -silent ");
    elif InfoLevel(InfoFSA)>1 then
       callstring := Concatenation(callstring," -v ");
    fi;
    callstring := Concatenation(callstring," ",filename);
    Info(InfoFSA,1,"Calling fsa determinization program.\n");
    Info(InfoFSA,3,"  ",callstring);
    Exec(callstring);
    Info(InfoFSA,1,"External fsa determinization program complete.\n");
    if not READ(Concatenation(_KBTmpFileName,".fsafordet.determinize")) then
       Error("Could not open determinized fsa file");
    fi;
    Exec(Concatenation("/bin/rm -f ",_KBTmpFileName,".fsafordet*"));
    InitializeFSA(_FSA_determinize);
    fsa.alphabet := alph;
    _FSA_min.alphabet := alph;
    return _FSA_determinize;
end;

#############################################################################
##
#F  MinimizeFSA(<fsa>) . . . call external program to minimize fsa <fsa>
##
## Minimized FSA is returned.
## Public function.
MinimizeFSA := function(fsa)
  local callstring, filename, alph;
    
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if  IsDeterministicFSA(fsa)=false  then
       Error("First argument is not a dfa.");
    fi;
    ## We replace the alphabet by simple-type alphabet for the
    ## I/O phase.
    alph := fsa.alphabet;
    fsa.alphabet := rec(type:="simple",size:=alph.size);
    InitializeSR(fsa.alphabet);
    filename := Concatenation(_KBTmpFileName,".fsaformin");
    WriteFSA(fsa,"_FSA",filename,";");
    callstring := Filename(_KBExtDir,"fsamin");
    if InfoLevel(InfoFSA)=0 then
       callstring := Concatenation(callstring," -silent ");
    elif InfoLevel(InfoFSA)>1 then
       callstring := Concatenation(callstring," -v ");
    fi;
    callstring := Concatenation(callstring," ",filename);
    Info(InfoFSA,1,"Calling fsa minimization program.\n");
    Info(InfoFSA,3,"  ",callstring);
    Exec(callstring);
    Info(InfoFSA,1,"External fsa minimization program complete.\n");
    if not READ(Concatenation(_KBTmpFileName,".fsaformin.min")) then
       Error("Could not open minimized fsa file");
    fi;
    Exec(Concatenation("/bin/rm -f ",_KBTmpFileName,".fsaformin*"));
    InitializeFSA(_FSA_min);
    fsa.alphabet := alph;
    _FSA_min.alphabet := alph;
    return _FSA_min;
end;

#############################################################################
##
#F  NotFSA(<fsa>) . . . call external program to negate fsa <fsa>
##
## An FSA is returned in which a word is accepted iff it is not
## accepted by <fsa>.
## Public function.
NotFSA := function(fsa)
  local callstring, filename, alph;
    
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if  IsDeterministicFSA(fsa)=false  then
       Error("First argument is not a dfa.");
    fi;
    ## We replace the alphabet by simple-type alphabet for the
    ## I/O phase.
    alph := fsa.alphabet;
    fsa.alphabet := rec(type:="simple",size:=alph.size);
    InitializeSR(fsa.alphabet);
    filename := Concatenation(_KBTmpFileName,".fsafornot");
    WriteFSA(fsa,"_FSA",filename,";");
    callstring := Filename(_KBExtDir,"fsanot");
    if InfoLevel(InfoFSA)=0 then
       callstring := Concatenation(callstring," -silent ");
    elif InfoLevel(InfoFSA)>1 then
       callstring := Concatenation(callstring," -v ");
    fi;
    callstring := Concatenation(callstring," ",filename);
    Info(InfoFSA,1,"Calling fsa `not' program.\n");
    Info(InfoFSA,3,"  ",callstring);
    Exec(callstring);
    Info(InfoFSA,1,"External fsa `not' program complete.\n");
    if not READ(Concatenation(_KBTmpFileName,".fsafornot.not")) then
       Error("Could not open `not' fsa file");
    fi;
    Exec(Concatenation("/bin/rm -f ",_KBTmpFileName,".fsafornot*"));
    InitializeFSA(_FSA_not);
    fsa.alphabet := alph;
    _FSA_not.alphabet := alph;
    return _FSA_not;
end;

#############################################################################
##
#F  StarFSA(<fsa>) . . . call external program to star fsa <fsa>
##
## An FSA is returned in which a word is accepted iff it is a
## concatenation of 0 or more words accepted by <fsa>.
## Public function.
StarFSA := function(fsa)
  local callstring, filename, alph;
    
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if  IsDeterministicFSA(fsa)=false  then
       Error("First argument is not a dfa.");
    fi;
    ## We replace the alphabet by simple-type alphabet for the
    ## I/O phase.
    alph := fsa.alphabet;
    fsa.alphabet := rec(type:="simple",size:=alph.size);
    InitializeSR(fsa.alphabet);
    filename := Concatenation(_KBTmpFileName,".fsaforstar");
    WriteFSA(fsa,"_FSA",filename,";");
    callstring := Filename(_KBExtDir,"fsastar");
    if InfoLevel(InfoFSA)=0 then
       callstring := Concatenation(callstring," -silent ");
    elif InfoLevel(InfoFSA)>1 then
       callstring := Concatenation(callstring," -v ");
    fi;
    callstring := Concatenation(callstring," ",filename);
    Info(InfoFSA,1,"Calling fsa `star' program.\n");
    Info(InfoFSA,3,"  ",callstring);
    Exec(callstring);
    Info(InfoFSA,1,"External fsa `star' program complete.\n");
    if not READ(Concatenation(_KBTmpFileName,".fsaforstar.star")) then
       Error("Could not open `star' fsa file");
    fi;
    Exec(Concatenation("/bin/rm -f ",_KBTmpFileName,".fsaforstar*"));
    InitializeFSA(_FSA_star);
    fsa.alphabet := alph;
    _FSA_star.alphabet := alph;
    return _FSA_star;
end;

#############################################################################
##
#F  ReverseFSA(<fsa>,[<subsets>]) . call external program to reverse fsa <fsa>
##
## An FSA is returned in which a word is accepted iff it is the reverses
## of a word accepted by <fsa>.
## If the optional 'subsets' argument is true, then the states of the
## returned fsa are given labels specifying the subsets of the original
## state-set to which they correspond.
## Public function.
ReverseFSA := function(arg)
  local callstring, filename, alph, fsa, subsets;
    
    fsa := arg[1];
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if  IsDeterministicFSA(fsa)=false  then
       Error("First argument is not a dfa.");
    fi;
    subsets := false;
    if Length(arg)>=2 and arg[2]=true then
      subsets:=true;
    fi;
    ## We replace the alphabet by simple-type alphabet for the
    ## I/O phase.
    alph := fsa.alphabet;
    fsa.alphabet := rec(type:="simple",size:=alph.size);
    InitializeSR(fsa.alphabet);
    filename := Concatenation(_KBTmpFileName,".fsaforreverse");
    WriteFSA(fsa,"_FSA",filename,";");
    callstring := Filename(_KBExtDir,"fsareverse");
    if InfoLevel(InfoFSA)=0 then
       callstring := Concatenation(callstring," -silent ");
    elif InfoLevel(InfoFSA)>1 then
       callstring := Concatenation(callstring," -v ");
    fi;
    if subsets then
      callstring := Concatenation(callstring," -s ");
    fi;
    callstring := Concatenation(callstring," ",filename);
    Info(InfoFSA,1,"Calling fsa `reverse' program.\n");
    Info(InfoFSA,3,"  ",callstring);
    Exec(callstring);
    Info(InfoFSA,1,"External fsa `reverse' program complete.\n");
    if not READ(Concatenation(_KBTmpFileName,".fsaforreverse.reverse")) then
       Error("Could not open `reverse' fsa file");
    fi;
    Exec(Concatenation("/bin/rm -f ",_KBTmpFileName,".fsaforreverse*"));
    InitializeFSA(_FSA_reverse);
    fsa.alphabet := alph;
    _FSA_reverse.alphabet := alph;
    return _FSA_reverse;
end;

#############################################################################
##
#F  ExistsFSA(<fsa>) . . . call external program to 'exist' fsa <fsa>
##
## Here <fsa> must be a 2-variable FSA.
## An FSA is returned in which a word  w1 is accepted iff 
## (w1,w2) is accepted by <fsa> for some word w2.
## Public function.
ExistsFSA := function(fsa)
  local callstring, filename, alph;
    
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if  IsDeterministicFSA(fsa)=false  then
       Error("First argument is not a dfa.");
    fi;
    if fsa.alphabet.type <> "product" or fsa.alphabet.arity <> 2 then
       Error("Alphabet of argument is not 2-variable.");
    fi;
    ## We replace the base alphabet by simple-type alphabet for the
    ## I/O phase.
    alph := fsa.alphabet.base;
    fsa.alphabet.base := rec(type:="simple",size:=alph.size);
    InitializeSR(fsa.alphabet.base);
    filename := Concatenation(_KBTmpFileName,".fsaforexists");
    WriteFSA(fsa,"_FSA",filename,";");
    callstring := Filename(_KBExtDir,"fsaexists");
    if InfoLevel(InfoFSA)=0 then
       callstring := Concatenation(callstring," -silent ");
    elif InfoLevel(InfoFSA)>1 then
       callstring := Concatenation(callstring," -v ");
    fi;
    callstring := Concatenation(callstring," ",filename);
    Info(InfoFSA,1,"Calling fsa `exists' program.\n");
    Info(InfoFSA,3,"  ",callstring);
    Exec(callstring);
    Info(InfoFSA,1,"External fsa `exists' program complete.\n");
    if not READ(Concatenation(_KBTmpFileName,".fsaforexists.exists")) then
       Error("Could not open `exists' fsa file");
    fi;
    Exec(Concatenation("/bin/rm -f ",_KBTmpFileName,".fsaforexists*"));
    InitializeFSA(_FSA_exists);
    fsa.alphabet.base := alph;
    _FSA_exists.alphabet := alph;
    return _FSA_exists;
end;

#############################################################################
##
#F  SwapCoordsFSA(<fsa>)
##     . . . call external program to swap coordinates of fsa <fsa>
##
## Here <fsa> must be a 2-variable FSA.
## An 2-variable FSA is returned in which (w1,w2) is accepted iff 
## (w2,w1) is accepted by <fsa>.
## Public function.
SwapCoordsFSA := function(fsa)
  local callstring, filename, alph;
    
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if  IsDeterministicFSA(fsa)=false  then
       Error("First argument is not a dfa.");
    fi;
    if fsa.alphabet.type <> "product" or fsa.alphabet.arity <> 2 then
       Error("Alphabet of argument is not 2-variable.");
    fi;
    ## We replace the base alphabet by simple-type alphabet for the
    ## I/O phase.
    alph := fsa.alphabet.base;
    fsa.alphabet.base := rec(type:="simple",size:=alph.size);
    InitializeSR(fsa.alphabet.base);
    filename := Concatenation(_KBTmpFileName,".fsaforswap_coords");
    WriteFSA(fsa,"_FSA",filename,";");
    callstring := Filename(_KBExtDir,"fsaswapcoords");
    if InfoLevel(InfoFSA)=0 then
       callstring := Concatenation(callstring," -silent ");
    elif InfoLevel(InfoFSA)>1 then
       callstring := Concatenation(callstring," -v ");
    fi;
    callstring := Concatenation(callstring," ",filename," ",filename,".o");
 #Print(callstring,"\n");
    Info(InfoFSA,1,"Calling fsa `swap_coords' program.\n");
    Info(InfoFSA,3,"  ",callstring);
    Exec(callstring);
    Info(InfoFSA,1,"External fsa `swap_coords' program complete.\n");
    if not
       READ(Concatenation(_KBTmpFileName,".fsaforswap_coords.o"))
          then Error("Could not open `swapcoords' fsa file");
    fi;
    Exec(Concatenation("/bin/rm -f ",_KBTmpFileName,".fsaforswap_coords*"));
    InitializeFSA(_FSA_swap_coords);
    fsa.alphabet.base := alph;
    _FSA_swap_coords.alphabet.base := alph;
    return _FSA_swap_coords;
end;

#############################################################################
##
#F  AndFSA(<fsa1>, <fsa2>) . . call external program to and fsa's <fsa1>,<fsa2>
##
## An FSA is returned in which a word is accepted iff it is a
## accepted by both of the fsa's <fsa1> and <fsa2>.
## Public function.
AndFSA := function(fsa1, fsa2)
  local callstring, filename1, filename2, filename3, alph;
    
    if not IsInitializedFSA(fsa1) then
       InitializeFSA(fsa1);
    fi;
    if not IsInitializedFSA(fsa2) then
       InitializeFSA(fsa2);
    fi;
    if  IsDeterministicFSA(fsa1)=false or IsDeterministicFSA(fsa2)=false then
       Error("One of the arguments is not a dfa.");
    fi;
    ## We replace the alphabet by simple-type alphabet for the
    ## I/O phase.
    alph := fsa1.alphabet;
    if alph <> fsa2.alphabet then
      Error("Arguments have different alphabets.");
    fi;
    fsa1.alphabet := rec(type:="simple",size:=alph.size);
    InitializeSR(fsa1.alphabet);
    fsa2.alphabet := rec(type:="simple",size:=alph.size);
    InitializeSR(fsa2.alphabet);
    filename1 := Concatenation(_KBTmpFileName,".fsaforand1");
    filename2 := Concatenation(_KBTmpFileName,".fsaforand2");
    filename3 := Concatenation(_KBTmpFileName,".fsaforand3");
    WriteFSA(fsa1,"_FSA",filename1,";");
    WriteFSA(fsa2,"_FSA",filename2,";");
    callstring := Filename(_KBExtDir,"fsaand");
    if InfoLevel(InfoFSA)=0 then
       callstring := Concatenation(callstring," -silent ");
    elif InfoLevel(InfoFSA)>1 then
       callstring := Concatenation(callstring," -v ");
    fi;
    callstring := Concatenation(callstring," ",
                     filename1," ",filename2," ",filename3);
    Info(InfoFSA,1,"Calling fsa `and' program.\n");
    Info(InfoFSA,3,"  ",callstring);
    Exec(callstring);
    Info(InfoFSA,1,"External fsa `and' program complete.\n");
    if not READ(filename3) then
       Error("Could not open `and' fsa file");
    fi;
    Exec(Concatenation("/bin/rm -f ",_KBTmpFileName,".fsaforand*"));
    InitializeFSA(_FSA_and);
    fsa1.alphabet := alph;
    fsa2.alphabet := alph;
    _FSA_and.alphabet := alph;
    return _FSA_and;
end;

#############################################################################
##
#F  OrFSA(<fsa1>, <fsa2>) . . . call external program to or fsa's <fsa1>,<fsa2>
##
## An FSA is returned in which a word is accepted iff it is a
## accepted by either of the fsa's <fsa1> or <fsa2>.
## Public function.
OrFSA := function(fsa1, fsa2)
  local callstring, filename1, filename2, filename3, alph;
    
    if not IsInitializedFSA(fsa1) then
       InitializeFSA(fsa1);
    fi;
    if not IsInitializedFSA(fsa2) then
       InitializeFSA(fsa2);
    fi;
    if  IsDeterministicFSA(fsa1)=false or IsDeterministicFSA(fsa2)=false then
       Error("One of the arguments is not a dfa.");
    fi;
    ## We replace the alphabet by simple-type alphabet for the
    ## I/O phase.
    alph := fsa1.alphabet;
    if alph <> fsa2.alphabet then
      Error("Arguments have different alphabets.");
    fi;
    fsa1.alphabet := rec(type:="simple",size:=alph.size);
    InitializeSR(fsa1.alphabet);
    fsa2.alphabet := rec(type:="simple",size:=alph.size);
    InitializeSR(fsa2.alphabet);
    filename1 := Concatenation(_KBTmpFileName,".fsaforor1");
    filename2 := Concatenation(_KBTmpFileName,".fsaforor2");
    filename3 := Concatenation(_KBTmpFileName,".fsaforor3");
    WriteFSA(fsa1,"_FSA",filename1,";");
    WriteFSA(fsa2,"_FSA",filename2,";");
    callstring := Filename(_KBExtDir,"fsaor");
    if InfoLevel(InfoFSA)=0 then
       callstring := Concatenation(callstring," -silent ");
    elif InfoLevel(InfoFSA)>1 then
       callstring := Concatenation(callstring," -v ");
    fi;
    callstring := Concatenation(callstring," ",
                     filename1," ",filename2," ",filename3);
    Info(InfoFSA,1,"Calling fsa `or' program.\n");
    Info(InfoFSA,3,"  ",callstring);
    Exec(callstring);
    Info(InfoFSA,1,"External fsa `or' program complete.\n");
    if not READ(filename3) then
       Error("Could not open `or' fsa file");
    fi;
    Exec(Concatenation("/bin/rm -f ",_KBTmpFileName,".fsaforor*"));
    InitializeFSA(_FSA_or);
    fsa1.alphabet := alph;
    fsa2.alphabet := alph;
    _FSA_or.alphabet := alph;
    return _FSA_or;
end;

#############################################################################
##
#F  ConcatFSA(<fsa1>, <fsa2>)
##            . . . call external program to concat fsa's <fsa1>,<fsa2>
##
## An FSA is returned in which a word is accepted iff it is the concatenation
## of words accepted by the fsa's <fsa1> and <fsa2>.
## Public function.
ConcatFSA := function(fsa1, fsa2)
  local callstring, filename1, filename2, filename3, alph;
    
    if not IsInitializedFSA(fsa1) then
       InitializeFSA(fsa1);
    fi;
    if not IsInitializedFSA(fsa2) then
       InitializeFSA(fsa2);
    fi;
    if  IsDeterministicFSA(fsa1)=false or IsDeterministicFSA(fsa2)=false then
       Error("One of the arguments is not a dfa.");
    fi;
    ## We replace the alphabet by simple-type alphabet for the
    ## I/O phase.
    alph := fsa1.alphabet;
    if alph <> fsa2.alphabet then
      Error("Arguments have different alphabets.");
    fi;
    fsa1.alphabet := rec(type:="simple",size:=alph.size);
    InitializeSR(fsa1.alphabet);
    fsa2.alphabet := rec(type:="simple",size:=alph.size);
    InitializeSR(fsa2.alphabet);
    filename1 := Concatenation(_KBTmpFileName,".fsaforconcat1");
    filename2 := Concatenation(_KBTmpFileName,".fsaforconcat2");
    filename3 := Concatenation(_KBTmpFileName,".fsaforconcat3");
    WriteFSA(fsa1,"_FSA",filename1,";");
    WriteFSA(fsa2,"_FSA",filename2,";");
    callstring := Filename(_KBExtDir,"fsaconcat");
    if InfoLevel(InfoFSA)=0 then
       callstring := Concatenation(callstring," -silent ");
    elif InfoLevel(InfoFSA)>1 then
       callstring := Concatenation(callstring," -v ");
    fi;
    callstring := Concatenation(callstring," ",
                     filename1," ",filename2," ",filename3);
    Info(InfoFSA,1,"Calling fsa `concat' program.\n");
    Info(InfoFSA,3,"  ",callstring);
    Exec(callstring);
    Info(InfoFSA,1,"External fsa `concat' program complete.\n");
    if not READ(filename3) then
       Error("Could not open `concat' fsa file");
    fi;
    Exec(Concatenation("/bin/rm -f ",_KBTmpFileName,".fsaforconcat*"));
    InitializeFSA(_FSA_concat);
    fsa1.alphabet := alph;
    fsa2.alphabet := alph;
    _FSA_concat.alphabet := alph;
    return _FSA_concat;
end;

#############################################################################
##
#F  LanguagesEqualFSA(<fsa1>, <fsa2>)
##            . . . decide whether  <fsa1>, <fsa2> havbe the same language
##
## <fsa1> and <fsa2> must have the same alphabet, or an error results.
## true or false is returned according to whether <fsa1> and <fsa2> have
## the same language.
## 
## Public function.
LanguagesEqualFSA := function(fsa1, fsa2)
    local mfsa1, mfsa2;
    if not IsInitializedFSA(fsa1) then
       InitializeFSA(fsa1);
    fi;
    if not IsInitializedFSA(fsa2) then
       InitializeFSA(fsa2);
    fi;
    if  IsDeterministicFSA(fsa1)=false or IsDeterministicFSA(fsa2)=false then
       Error("One of the arguments is not a dfa.");
    fi;
    if fsa1.alphabet <> fsa2.alphabet then
      Error("Parameters do not have the same alphabet.");
    fi;

    mfsa1 := MinimizeFSA(fsa1);
    mfsa2 := MinimizeFSA(fsa2);
    BFSFSA(mfsa1);
    BFSFSA(mfsa2);
    return DenseDTableFSA(mfsa1) = DenseDTableFSA(mfsa2);
end;

#############################################################################
##
#F  GrowthFSA(<fsa>) . . . call external program to find growth function
##                         of <fsa>
##
## A rational function is returned. The coefficient of x^n in this function is
## the number of words of length n in the language of <fsa>,
## 
## Public function.
GrowthFSA := function(fsa)
  local callstring, filename, alph, gf;
    
    if not IsInitializedFSA(fsa) then
       InitializeFSA(fsa);
    fi;
    if  IsDeterministicFSA(fsa)=false  then
       Error("First argument is not a dfa.");
    fi;
    ## We replace the alphabet by simple-type alphabet for the
    ## I/O phase.
    alph := fsa.alphabet;
    fsa.alphabet := rec(type:="simple",size:=alph.size);
    InitializeSR(fsa.alphabet);
    filename := Concatenation(_KBTmpFileName,".fsaforgrowth");
    WriteFSA(fsa,"_FSA",filename,";");
    callstring := Filename(_KBExtDir,"fsagrowth");
    if InfoLevel(InfoFSA)>1 then
       callstring := Concatenation(callstring," -v ");
    fi;
    callstring := Concatenation(callstring," ",filename);
    Info(InfoFSA,1,"Calling fsa `growth' program.\n");
    Info(InfoFSA,3,"  ",callstring);
    Exec(callstring);
    Info(InfoFSA,1,"External fsa `growth' program complete.\n");
    gf := ReadAsFunction(Concatenation(_KBTmpFileName,".fsaforgrowth.growth"));
    Exec(Concatenation("/bin/rm -f ",_KBTmpFileName,".fsaforgrowth*"));
    fsa.alphabet := alph;
    if gf=fail then
      return fail;
    fi;
    return gf();
end;
