#############################################################################
##
#A  util.g                  GAP library
##
##  This file contains the machinery for calling the external `C' programs
##  of the kbmag standalone, and for cleaning up after them.
##

#############################################################################
#V  _KBExtDir      directory containing the external programs
#V  _KBTmpFileName base name of the temporary files used to talk to them
_KBExtDir  :=  DirectoriesPackagePrograms("kbmag");
_KBTmpFileName := TmpName();

#############################################################################
##
#F  _KBExec(<info>, <prog>, <args>) . . run one of the external kbmag programs
##
##  <args> is a list of strings, passed to <prog> as its arguments; no shell
##  is involved, so no quoting is needed. The exit status is returned.
##  Private function.
_KBExec := function ( info, prog, args )
    local  path;
    path := Filename(_KBExtDir, prog);
    if path = fail then
      Error("The external program `", prog, "' was not found. ",
            "Did you compile the kbmag package?");
    fi;
    Info(info, 3, "  ", path, " ", JoinStringsWithSeparator(args, " "));
    return Process(DirectoryCurrent(), path,
                   InputTextUser(), OutputTextUser(), args);
end;

#############################################################################
##
#F  _KBExecChecked(<info>, <prog>, <args>) . . as _KBExec, but insist on success
##
##  Only for those programs whose sole nonzero exit status means failure.
##  Private function.
_KBExecChecked := function ( info, prog, args )
    local  status;
    status := _KBExec(info, prog, args);
    if status <> 0 then
      Error("The external program `", prog, "' failed with exit status ",
            status, ".");
    fi;
end;

#############################################################################
##
#F  _KBRemoveTmpFiles(<prefix>) . . remove all files whose name starts <prefix>
##
##  This replaces the `rm -f <prefix>*' the package used to shell out for.
##  Private function.
_KBRemoveTmpFiles := function ( prefix )
    local  pos, dir, base, file;
    pos := Length(prefix);
    while pos > 0 and prefix[pos] <> '/' do pos := pos - 1; od;
    dir := prefix{[1..pos]};
    base := prefix{[pos+1..Length(prefix)]};
    if base = "" then
      Error("_KBRemoveTmpFiles needs a nonempty file name prefix.");
    fi;
    if dir = "" then dir := "./"; fi;
    for file in DirectoryContents(dir) do
      if Length(file) >= Length(base) and file{[1..Length(base)]} = base then
        RemoveFile(Concatenation(dir, file));
      fi;
    od;
end;
