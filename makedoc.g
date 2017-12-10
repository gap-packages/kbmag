##  makedoc.g,  version 06/12/17
##  This builds the documentation of the KBMag package
##  Needs: GAPDoc package, latex, pdflatex, mkindex
##  
LoadPackage( "GAPDoc" );

MakeGAPDocDoc( "doc",      # path to the directory containing the main file
               "manual",   # the name of the main file (without extension)
                           # list of (probably source code) files relative 
                           # to path which contain pieces of documentation 
                           # which must be included in the document
               [ "../PackageInfo.g" ], 
               "kbmag",    # the name of the book used by GAP's online help
               "../../..", # optional: relative path to the main GAP root 
                           # directory to produce HTML files with relative 
                           # paths to external books.
                           # optional: use "MathJax", "Tth" and/or "MathML"
                           # to produce additional variants of HTML files
               "MathJax"   # optional: use "MathJax", "Tth" and/or "MathML"
                           # to produce additional variants of HTML files
               );; 

# Copy the *.css and *.js files from the styles directory of the GAPDoc 
# package into the directory containing the package manual.
CopyHTMLStyleFiles( "doc" );

# Create the manual.lab file which is needed if the main manuals or another 
# package is referring to your package
GAPDocManualLab( "kbmag" );; 
