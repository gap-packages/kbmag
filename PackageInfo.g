SetPackageInfo( rec(

PackageName := "kbmag",
Subtitle := "Knuth-Bendix on Monoids and Automatic Groups",
Version := "1.5",
Date := "06/01/2009",

Persons := [
  rec( 
    LastName := "Holt",
    FirstNames := "Derek",
    IsAuthor      := true,
    IsMaintainer  := true,
    Email := "D.F.Holt@warwick.ac.uk",
    WWWHome := "http://homepages.warwick.ac.uk/staff/D.F.Holt/",
    PostalAddress := Concatenation( [
                       "Mathematics Institute\n",
                       "University of Warwick\n",
                       "Coventry CV4 7AL\n", "UK" ] )
  )
],

Status := "accepted",
CommunicatedBy := "Charles Wright (Oregon)",
AcceptDate := "07/2003",

SourceRepository := rec(
    Type := "git",
    URL := Concatenation( "https://github.com/gap-packages/", ~.PackageName ),
),
IssueTrackerURL := Concatenation( ~.SourceRepository.URL, "/issues" ),

PackageWWWHome := Concatenation( "https://gap-packages.github.io/", ~.PackageName ),
README_URL     := Concatenation( ~.PackageWWWHome, "/README" ),
PackageInfoURL := Concatenation( ~.PackageWWWHome, "/PackageInfo.g" ),
ArchiveURL     := Concatenation( ~.SourceRepository.URL,
                                "/releases/download/v", ~.Version,
                                "/", ~.PackageName ,"-", ~.Version),
ArchiveFormats := ".tar.gz",

AbstractHTML := 
  "The <span class=\"pkgname\">kbmag</span> package is a\
       <span class=\"pkgname\">GAP</span> interface to some `C' programs\
   for running the Knuth-Bendix completion program on finite semigroup,\
   monoid or group presentations, and for attempting to compute  automatic\
   structures of finitely presented groups",


PackageDoc := rec(
  BookName  := "kbmag",
  ArchiveURLSubset := ["doc", "htm"],
  HTMLStart := "htm/chapters.htm",
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "Knuth-Bendix on Monoids and Automatic Groups",
  Autoload  := true
),


Dependencies := rec(
  GAP := ">=4.7",
  NeededOtherPackages := [],
  SuggestedOtherPackages := [],
  ExternalConditions := ["Unix only"]
),

AvailabilityTest := function()
  local path,file;
    # test for existence of the compiled binary
    path:=DirectoriesPackagePrograms("kbmag");
    file:=Filename(path,"kbprog");
    if file=fail then
      Info(InfoWarning,1,
     "Package ``kbmag'': The program `kbprog' (for example) is not compiled");
      Info(InfoWarning,1,
        "`kbmag' is thus unavailable");
      Info(InfoWarning,1,
        "See the installation instructions; ",
        "type: ?Installing the package");
      return fail;
    fi;
    return true;
  end,

Autoload := false,

Keywords := [
  "Knuth-Bendix",
  "Automatic Groups"
]

#TestFile := "tst/testall.g",

));
