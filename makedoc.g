##  makedoc.g for the KBMag package
##  this creates the package documentation  
##  needs: GAPDoc and AutoDoc packages, latex, pdflatex, mkindex 
##  call this with GAP from within the package root directory 
##  
LoadPackage( "GAPDoc" );

if fail = LoadPackage("AutoDoc", ">= 2017.09.08") then
    Error("AutoDoc is required: version at least 2017.09.08");
fi;

AutoDoc( rec( 
    scaffold := rec(
        ## MainPage := false, 
        includes := [ "intro.xml", "rws.xml", "cosets.xml", "standalone.xml" ],
        entities := rec( 
            KBMAG := "<Package>KBMag</Package>",
            rkbp := "<M>{\\sf rkbp}</M>",
            Automata := "<M>{\\sf Automata}</M>", 
            fsa := "<M>{\\sf fsa}</M>",
            fsa1 := "<M>{\\sf fsa1}</M>",
            fsa2 := "<M>{\\sf fsa2}</M>",
            rws := "<M>{\\sf rws}</M>",
            ordering := "<M>{\\bf ordering}</M>",
            shortlex := "<M>{\\bf shortlex}</M>",
            wtlex := "<M>{\\bf wtlex}</M>",
            wreathprod := "<M>{\\bf wreathprod}</M>",
            recursive := "<M>{\\bf recursive}</M>"
        )
    )
));

# Create VERSION file for "make towww"
PrintTo( "VERSION", GAPInfo.PackageInfoCurrent.Version );

QUIT;
