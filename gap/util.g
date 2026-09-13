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
#F  _KBVerbosityFlags(<info>) . . . verbosity flags matching the level of <info>
##
##  Private function.
_KBVerbosityFlags := function ( info )
    if InfoLevel(info) = 0 then
      return ["-silent"];
    elif InfoLevel(info) = 2 then
      return ["-v"];
    elif InfoLevel(info) > 2 then
      return ["-vv"];
    fi;
    return [];
end;

#############################################################################
##
#F  _KBAutomatic(<info>, <cosets>, <large>, <filestore>, <diff1>)
##                  . . . . compute an automatic structure, or one on cosets
##
##  Does what the standalone scripts autgroup, resp. autcos, do for the files
##  named by _KBTmpFileName: Knuth-Bendix, the word-acceptor and multiplier
##  automata, then the axiom check. Returns whether the axioms hold.
##  Private function.
_KBAutomatic := function ( info, cosets, large, filestore, diff1 )
    local  verbosity, kbprog, files, time, flags, status;
    verbosity := _KBVerbosityFlags(info);
    if cosets then
      kbprog := "kbprogcos";
      files := [_KBTmpFileName, "cos"];
      time := "30";
    else
      kbprog := "kbprog";
      files := [_KBTmpFileName];
      time := "20";
    fi;

    # try small limits first, then larger ones
    status := 1;
    if not large then
      flags := ["-mt", "5", "-hf", "100", "-t", time, "-me", "200",
                "-ms", "1000", "-wd"];
      status := _KBExec(info, kbprog,
                        Concatenation(flags, verbosity, files));
    fi;
    if status <> 0 then
      flags := ["-mt", "20", "-hf", "100", "-cn", "0", "-wd"];
      if large then
        Append(flags, ["-me", "262144", "-t", "500"]);
      fi;
      status := _KBExec(info, kbprog,
                        Concatenation(flags, verbosity, files));
      if status <> 0 then
        Info(info, 1, "Knuth-Bendix program failed or was inconclusive.");
        return false;
      fi;
    fi;

    flags := [];
    if cosets then Add(flags, "-cos"); fi;
    if large then Add(flags, "-l"); fi;
    if diff1 then Add(flags, "-diff1"); fi;
    # autcos passes <filestore> to gpaxioms only
    if filestore and not cosets then Add(flags, "-f"); fi;
    status := _KBExec(info, "gpmakefsa",
                      Concatenation(flags, verbosity, files));
    if status <> 0 then
      Info(info, 1, "Constructing the automata failed.");
      return false;
    fi;

    flags := [];
    if cosets then Add(flags, "-cos"); fi;
    if large then Add(flags, "-l"); fi;
    if filestore then Append(flags, ["-f", "-ip", "s"]); fi;
    status := _KBExec(info, "gpaxioms",
                      Concatenation(flags, verbosity, files));
    if status = 2 then
      Info(InfoWarning, 1, "kbmag: verifying the axioms failed, ",
           "please report this example");
    fi;
    return status = 0;
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
