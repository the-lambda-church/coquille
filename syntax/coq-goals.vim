" Vim syntax file
" Language:     Coq-goals
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
elseif exists("b:current_syntax") && b:current_syntax == "coq-goals"
 finish
endif

" Coq is case sensitive.
syn case match

" Various
" syn match   coqError             "\S\+"
syn match   coqVernacPunctuation ":=\|\.\|:"
syn match   coqIdent             contained "[_[:alpha:]][_'[:alnum:]]*"

" Number of goals
syn match   coqNumberGoals       '\d\+ subgoals\?' nextgroup=coqGoal

" Hypothesis
syn region  coqHypothesisBlock  contains=coqHypothesis start="^[_[:alpha:]][_'[:alnum:]]*\s*:" end="^$" keepend
syn region  coqHypothesis       contained contains=coqHypothesisBody matchgroup=coqIdent start="^[_[:alpha:]][_'[:alnum:]]*" matchgroup=NONE end="^\S"me=e-1
syn region  coqHypothesisBody   contained contains=@coqTerm matchgroup=coqVernacPunctuation start=":" matchgroup=NONE end="^\S"me=e-1

" Separator
syn match   coqGoalNumber       contained "(\s*\d\+\s*\/\s*\d\+\s*)"
syn region  coqGoalSep          matchgroup=coqGoalLine start='^=\+' matchgroup=NONE end='^$' contains=coqGoalSepNumber
syn region  coqGoalSepNumber    matchgroup=coqGoalNumber start="(\s*\d\+\s*\/\s*\d\+\s*)" matchgroup=NONE end="^$" contains=@coqTerm

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

" Various (High priority)
syn region  coqString            start=+"+ skip=+""+ end=+"+ extend

" Synchronization
syn sync minlines=50
syn sync maxlines=500

" Define the default highlighting.
" For version 5.7 and earlier: only when not done already
" For version 5.8 and later: only when an item doesn't have highlighting yet
if version >= 508 || !exists("did_coq_goals_syntax_inits")
 if version < 508
  let did_coq_goals_syntax_inits = 1
  command -nargs=+ HiLink hi link <args>
 else
  command -nargs=+ HiLink hi def link <args>
 endif

 " TERMS AND TYPES
 HiLink coqTerm                      Type
 HiLink coqKwd             coqTerm
 HiLink coqTermPunctuation coqTerm

 " WORK LEFT
 HiLink coqNumberGoals               Todo
 HiLink coqGoalLine                  Todo

 " GOAL IDENTIFIER
 HiLink coqGoalNumber                Underlined

 " USUAL VIM HIGHLIGHTINGS
 " Comments
 HiLink coqComment                   Comment

 " Strings
 HiLink coqString                    String

 delcommand HiLink
endif

let b:current_syntax = "coq-goals"
