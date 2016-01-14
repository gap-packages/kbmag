#############################################################################
##
#W    init.g   share package 'kbmag'      Derek Holt
##
##    @(#)$Id: init.g,v 1.4 2001/01/10 01:00:43 gap Exp $
##

# announce the package version and test for the existence of the binary
DeclarePackage("kbmag","0.1",
  function()
  local path,file;
    # test for existence of the compiled binary
    path:=DirectoriesPackagePrograms("kbmag");
    file:=Filename(path,"kbprog");
    if file=fail then
      Info(InfoWarning,1,
        "Package ``kbmag'': The program `kbprog' is not compiled");
    fi;
    return file<>fail;
  end);


# install the documentation
DeclarePackageDocumentation( "kbmag", "doc" );

