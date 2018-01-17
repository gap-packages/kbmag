##  makedoc.g for the KBMag package
##  this creates the package documentation  
##  needs: GAPDoc and AutoDoc packages, latex, pdflatex, mkindex 
##  call this with GAP from within the package root directory 
##  
LoadPackage( "AutoDoc" );
LoadPackage( "kbmag" ); 

AutoDoc( rec( 
    scaffold := rec(
        ## MainPage := false, 
        includes := [ "intro.xml", "rws.xml", "cosets.xml", "standalone.xml" ],
        entities := rec( 
            AutoDoc := "<Package>AutoDoc</Package>",
            Automata := "<Package>Automata</Package>", 
            KBMAG := "<Package>KBMag</Package>",
            fsa := "<M>{\\sf fsa}</M>",
            fsa1 := "<M>{\\sf fsa1}</M>",
            fsa2 := "<M>{\\sf fsa2}</M>",
            rkbp := "<M>{\\sf rkbp}</M>",
            rws := "<M>{\\sf rws}</M>",
            ordering := "<B>ordering</B>",
            recursive := "<B>recursive</B>",
            shortlex := "<B>shortlex</B>",
            wtlex := "<B>wtlex</B>",
            wreathprod := "<B>wreathprod</B>"
        )
    )
));

QUIT;
