SetPackageInfo( rec(

PackageName := "kbmag",
Subtitle := "Knuth-Bendix on Monoids and Automatic Groups",
Version := "1.5.11",
Date := "03/01/2023", # dd/mm/yyyy format
License := "GPL-2.0-or-later",

Persons := [
  rec(
    LastName := "Holt",
    FirstNames := "Derek",
    IsAuthor      := true,
    IsMaintainer  := false,
    Email := "D.F.Holt@warwick.ac.uk",
    WWWHome := "https://homepages.warwick.ac.uk/staff/D.F.Holt/",
    PostalAddress := Concatenation( [
                       "Mathematics Institute\n",
                       "University of Warwick\n",
                       "Coventry CV4 7AL\n", "UK" ] )
  ),

  rec(
    LastName      := "GAP Team",
    FirstNames    := "The",
    IsAuthor      := false,
    IsMaintainer  := true,
    Email         := "support@gap-system.org",
  ),
],

Status := "accepted",
CommunicatedBy := "Charles Wright (Oregon)",
AcceptDate := "07/2003",

SourceRepository := rec(
    Type := "git",
    URL := Concatenation( "https://github.com/gap-packages/", ~.PackageName ),
),
IssueTrackerURL := Concatenation( ~.SourceRepository.URL, "/issues" ),
PackageWWWHome  := Concatenation( "https://gap-packages.github.io/", ~.PackageName ),
README_URL      := Concatenation( ~.PackageWWWHome, "/README.md" ),
PackageInfoURL  := Concatenation( ~.PackageWWWHome, "/PackageInfo.g" ),
ArchiveURL      := Concatenation( ~.SourceRepository.URL,
                                 "/releases/download/v", ~.Version,
                                 "/", ~.PackageName, "-", ~.Version ),
ArchiveFormats := ".tar.gz",

AbstractHTML :=
  "The <span class=\"pkgname\">kbmag</span> package is a\
       <span class=\"pkgname\">GAP</span> interface to some `C' programs\
   for running the Knuth-Bendix completion program on finite semigroup,\
   monoid or group presentations, and for attempting to compute automatic\
   structures of finitely presented groups",

PackageDoc := rec(
  BookName  := "kbmag",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0_mj.html",
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "Knuth-Bendix on Monoids and Automatic Groups",
  Autoload  := true
),


Dependencies := rec(
  GAP := ">=4.7",
  NeededOtherPackages := [ ],
  SuggestedOtherPackages := [ ],
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
],

TestFile := "tst/testall.g",

AutoDoc := rec(
    TitlePage := rec(
        Copyright := Concatenation(
            "&copyright; 1997 by Derek Holt<P/>\n\n",
            "This package may be distributed under the terms and conditions ",
            "of the GNU Public License Version 2.\n"
            ),
        Abstract := Concatenation( 
            "The &KBMAG; package is a &GAP; interface to some `C' ",
            "programs for running the Knuth-Bendix completion program ", 
            "on finite semigroup, monoid or group presentations, ", 
            "and for attempting to compute  automatic structures ", 
            "of finitely presented groups.<P/>", 
            "Bug reports, comments, suggestions for additional features, and ", 
            "offers to implement some of these, will all be very welcome.<P/>", 
            "Please submit any issues at ", 
            "<URL>https://github.com/gap-packages/kbmag/issues/</URL>.<P/>" 
            ), 
        Acknowledgements := Concatenation( 
            "This documentation was prepared with the ", 
            "&GAPDoc; <Cite Key='GAPDoc'/> and ", 
            "&AutoDoc; <Cite Key='AutoDoc'/> packages.<P/>\n", 
            "The procedure used to produce new releases uses the package ", 
            "<Package>GitHubPagesForGAP</Package> ", 
            "<Cite Key='GitHubPagesForGAP' /> ", 
            "and the package <Package>ReleaseTools</Package>.<P/>" 
            ),
    ) 
),

));
