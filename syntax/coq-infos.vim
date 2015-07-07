" Vim syntax file
" Language:     Coq-infos
" Filenames:    *.v
" Maintainer:  Vincent Aravantinos <vincent.aravantinos@gmail.com>
" Last Change: 2008 Dec 02 - Added the Program and Obligation constructions (in Coq v8.2) - with Serge Leblanc.
"              2008 Jan 30 - Applied the improvments for all constructions, added 'with' and 'where' for
"                            fixpoints and inductives, fixed some hard long standing bugs.
"              2008 Jan 27 - Changed the way things are coloured, improved the efficiency of colouring.
"              2008 Jan 25 - Added Ltac, added Notations, bugfixes.
"              2007 Dec 1 - Added Record's.
"              2007 Nov 28 - Added things to reuse (in other plugins) the knowledge that we are inside a proof.
"              2007 Nov 19 - Fixed bug with comments.
"              2007 Nov 17 - Various minor bugfixes.
"              2007 Nov 8 - Added keywords.
"              2007 Nov 8 - Fixed some ill-highlighting in the type of declarations.
"              2007 Nov 8 - Fixed pb with keywords ("\<...\>" had been forgotten) 
"                           (thanks to Vasileios Koutavas)
"              2007 Nov 8 - Definition...Defined now works as expected, 
"                           fixed a bug with tactics that were not recognized,
"                           fixed other bugs
"              2007 Nov 7 - Complete refactoring, (much) more accurate highlighting. Much bigger file...
"              2007 Nov 7 - Added tactic colouration, added other keywords (thanks to Tom Harke)
"              2007 Nov 6 - Added "Defined" keyword (thanks to Serge Leblanc)
"              2007 Nov 5 - Initial version.
" License:     public domain
" TODO: mark bad constructions (eg. Section ended but not opened)

" For version 5.x: Clear all syntax items
" For version 6.x: Quit when a syntax file was already loaded
if version < 600
 syntax clear
elseif exists("b:current_syntax") && b:current_syntax == "coq-infos"
 finish
endif

" Coq is case sensitive.
syn case match

syn cluster coqVernac contains=coqRequire,coqCheck,coqEval,coqNotation,coqTacNotation,coqDecl,coqThm,coqLtacDecl,coqDef,coqFix,coqInd,coqRec,coqShow

" Various
syn match   coqVernacPunctuation ":=\|\.\|:"
syn match   coqIdent             contained "[_[:alpha:]][_'[:alnum:]]*"
syn keyword coqTopLevel          Declare Type Canonical Structure Cd Coercion Derive Drop Existential
"...
syn keyword coqVernacCmd         Functional Scheme Back Combined
syn keyword coqFeedback          Show About Print

" Terms
syn cluster coqTerm            contains=coqKwd,coqTermPunctuation,coqKwdMatch,coqKwdLet,coqKwdParen
syn region coqKwdMatch         contained contains=@coqTerm matchgroup=coqKwd start="\<match\>" end="\<with\>"
syn region coqKwdLet           contained contains=@coqTerm matchgroup=coqKwd start="\<let\>"   end=":="
syn region coqKwdParen         contained contains=@coqTerm matchgroup=coqTermPunctuation start="(" end=")" keepend extend
syn keyword coqKwd             contained else end exists2 fix forall fun if in struct then as return
syn match   coqKwd             contained "\<where\>"
syn match   coqKwd             contained "\<exists!\?"
syn match   coqKwd             contained "|\|/\\\|\\/\|<->\|\~\|->\|=>\|{\|}\|&\|+\|-\|*\|=\|>\|<\|<="
syn match coqTermPunctuation   contained ":=\|:>\|:\|;\|,\|||\|\[\|\]\|@\|?\|\<_\>"

" Compute
syn region coqComputed  contains=@coqTerm matchgroup=coqVernacPunctuation start="^\s*=" matchgroup=NONE end="^$"

" Definitions
syn region coqDefName          start="[_[:alpha:]][_'[:alnum:]]*" skip="\%(=\|:\)" end="\%(=\|:\)"me=e-1 contains=coqDefContents1,coqDefContents2
syn region coqDefContents1     contained contains=@coqTerm matchgroup=coqVernacPunctuation start=":" matchgroup=NONE end="^$"  matchgroup=NONE end="^\S"me=e-1
syn region coqDefContents2     contained contains=@coqTerm matchgroup=coqVernacPunctuation start="=" matchgroup=NONE end="^$"

" Notations
syn region coqNotationDef       contains=coqNotationString,coqNotationTerm matchgroup=coqVernacCmd start="\<Notation\>\%(\s*\<Scope\>\)\?" end="^$"
syn region coqNotationTerm      contained matchgroup=coqVernacPunctuation start=":=" matchgroup=NONE end="\""me=e-1 end="^$"me=e-1 contains=coqNotationScope,coqNotationFormat
syn region coqNotationScope     contained contains=@coqTerm,coqNotationFormat matchgroup=coqVernacPunctuation start=":" end="\""me=e-1 end="^$"
syn region coqNotationFormat    contained contains=coqNotationKwd,coqString matchgroup=coqVernacPunctuation start="(" end=")"

syn match   coqNotationKwd contained "at \(next \)\?level"
syn match   coqNotationKwd contained "\(no\|left\|right\) associativity"
syn match   coqNotationKwd contained "only parsing"
syn match   coqNotationKwd contained "default interpretation"
syn match   coqNotationKwd contained "(\|,\|)\|:"
syn keyword coqNotationKwd contained ident global bigint format

syn region coqNotationString contained start=+"+ skip=+""+ end=+"+ extend

"Inductives and Constants
syn region coqInd            contains=coqIndBody start="\<\%(\%(Co\)\?Inductive\|Constant\)\>" matchgroup=coqVernacPunctuation end="^\S"me=e-1 keepend
syn region coqIndBody     contained contains=coqIdent,coqIndTerm,coqIndBinder matchgroup=coqVernacCmd start="\%(Co\)\?Inductive\|Constant" start="\<with\>" matchgroup=NONE end="^\S"me=e-1
syn region coqIndBinder      contained contains=coqIndBinderTerm matchgroup=coqVernacPunctuation start="("  end=")" keepend
syn region coqIndBinderTerm  contained contains=@coqTerm matchgroup=coqVernacPunctuation start=":" end=")"
syn region coqIndTerm        contained contains=@coqTerm,coqIndContent matchgroup=coqVernacPunctuation start=":" matchgroup=NONE end="^\S"me=e-1
syn region coqIndContent     contained contains=coqIndConstructor start=":=" end="^\S"me=e-1
syn region coqIndConstructor contained contains=coqConstructor,coqIndBinder,coqIndConsTerm,coqIndNot,coqIndBody matchgroup=coqVernacPunctuation start=":=\%(\_s*|\)\?" start="|" matchgroup=NONE end="^\S"me=e-1
syn region coqIndConsTerm    contained contains=coqIndBody,@coqTerm,coqIndConstructor,coqIndNot matchgroup=coqConstructor start=":" matchgroup=NONE end="^\S"me=e-1
syn region coqIndNot         contained contains=coqNotationString,coqIndNotTerm matchgroup=coqVernacCmd start="\<where\>" end="^\S"me=e-1
syn region coqIndNotTerm     contained contains=@coqTerm,coqIndNotScope,coqIndBody matchgroup=coqVernacPunctuation start=":=" end="^\S"me=e-1
syn region coqIndNotScope    contained contains=coqIndBody matchgroup=coqVernacPunctuation start=":" end="^\S"me=e-1
syn match  coqConstructor    contained "[_[:alpha:]][_'[:alnum:]]*"

" Records
syn region coqRec        contains=coqRecProfile start="\<Record\>" matchgroup=coqVernacPunctuation end="^\S"me=e-1 keepend
syn region coqRecProfile contained contains=coqIdent,coqRecTerm,coqRecBinder matchgroup=coqVernacCmd start="Record" matchgroup=NONE end="^\S"me=e-1
syn region coqRecBinder  contained contains=@coqTerm matchgroup=coqTermPunctuation start="("  end=")"
syn region coqRecTerm    contained contains=@coqTerm,coqRecContent matchgroup=coqVernacPunctuation start=":"  end="^\S"me=e-1
syn region coqRecContent contained contains=coqConstructor,coqRecStart matchgroup=coqVernacPunctuation start=":=" end="^\S"me=e-1
syn region coqRecStart   contained contains=coqRecField,@coqTerm start="{" matchgroup=coqVernacPunctuation end="}" keepend
syn region coqRecField   contained contains=coqField matchgroup=coqVernacPunctuation start="{" end=":"
syn region coqRecField   contained contains=coqField matchgroup=coqVernacPunctuation start=";" end=":"
syn match coqField       contained "[_[:alpha:]][_'[:alnum:]]*"

" Warning and errors
syn match   coqBad               contained ".*\%(w\|W\)arnings\?"
syn match   coqVeryBad           contained ".*\%(e\|E\)rrors\?"
syn region  coqWarningMsg        matchgroup=coqBad start="^.*\%(w\|W\)arnings\?:" end="$"
syn region  coqErrorMsg          matchgroup=coqVeryBad start="^.*\%(e\|E\)rrors\?:" end="$"

" Various (High priority)
syn region  coqComment           containedin=ALL contains=coqComment,coqTodo start="(\*" end="\*)" extend keepend
syn keyword coqTodo              contained TODO FIXME XXX NOTE
syn region  coqString            start=+"+ skip=+""+ end=+"+ extend

" Synchronization
syn sync minlines=50
syn sync maxlines=500

" Define the default highlighting.
" For version 5.7 and earlier: only when not done already
" For version 5.8 and later: only when an item doesn't have highlighting yet
if version >= 508 || !exists("did_coq_syntax_inits")
 if version < 508
  let did_coq_syntax_inits = 1
  command -nargs=+ HiLink hi link <args>
 else
  command -nargs=+ HiLink hi def link <args>
 endif

 " PROOFS
 HiLink coqTactic                    Keyword
 HiLink coqLtac coqTactic
 HiLink coqProofKwd coqTactic
 HiLink coqProofPunctuation coqTactic
 HiLink coqTacticKwd coqTactic
 HiLink coqTacNotationKwd coqTactic
 HiLink coqEvalFlag coqTactic
 " Exception
 HiLink coqProofDot coqVernacular

 " PROOF DELIMITERS ("Proof", "Qed", "Defined", "Save")
 HiLink coqProofDelim                Underlined

 " TERMS AND TYPES
 HiLink coqTerm                      Type
 HiLink coqKwd             coqTerm
 HiLink coqTermPunctuation coqTerm

 " VERNACULAR COMMANDS
 HiLink coqVernacular                PreProc
 HiLink coqVernacCmd         coqVernacular
 HiLink coqVernacPunctuation coqVernacular
 HiLink coqHint              coqVernacular
 HiLink coqFeedback          coqVernacular
 HiLink coqTopLevel          coqVernacular

 " DEFINED OBJECTS
 HiLink coqIdent                     Identifier
 HiLink coqDefName                   Identifier
 HiLink coqNotationString coqIdent

 " CONSTRUCTORS AND FIELDS
 HiLink coqConstructor               Keyword
 HiLink coqField coqConstructor

 " NOTATION SPECIFIC ("at level", "format", etc)
 HiLink coqNotationKwd               Special

 " WARNINGS AND ERRORS
 HiLink coqBad                       WarningMsg
 HiLink coqVeryBad                   ErrorMsg
 HiLink coqWarningMsg                WarningMsg
 HiLink coqBad                       WarningMsg


 " USUAL VIM HIGHLIGHTINGS
   " Comments
   HiLink coqComment                   Comment
   HiLink coqProofComment coqComment

   " Todo
   HiLink coqTodo                      Todo

   " Errors
   HiLink coqError                     Error

   " Strings
   HiLink coqString                    String

 delcommand HiLink
endif

let b:current_syntax = "coq-infos"
