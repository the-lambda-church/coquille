Coquille
========

Coquille is a vim plugin aiming to bring the interactivity of CoqIDE into your
favorite editor.

Installation
------------

This repository is meant to be used as a [pathogen][1] bundle. If you don't
already use pathogen, I strongly recommand that you start right now.

As everybody knows, vim is a wonderful editor which offers no way for a plugin
to track modifications on a buffer. For that reason Coquille depends on a set of
heuristicts collected in [vimbufsync][2] to detect modifications in the buffer.
You will need to make this plugin available in your runtime path (it can be
installed as a pathogen bundle as well) if you want Coquille to work.

Once that is done, installing Coquille is just as simple as doing :

    cd ~/.vim/bundle
    git clone https://github.com/trefis/coquille.git

Not that by default, you will be in the `pathogen-bundle` branch, which also
ships Vincent Aravantinos [syntax][3] and [indent][4] scripts for Coq, as well
as an ftdetect script.
If you already have those in your vim config, then just switch to the master
branch.

Getting started
---------------

To launch Coquille on your Coq file, run `:CoqLaunch` which will make the
commands :

- CoqNext
- CoqToCursor
- CoqUndo
- CoqKill

available to you.

By default Coquille forces no mapping for these commands, however two sets of
mapping are already defined and you can activate them by adding :

    " Maps Coquille commands to CoqIDE default key bindings
    au FileType coq call coquille#CoqideMapping()

or

    " Maps Coquille commands to <F2> (Undo), <F3> (Next), <F4> (ToCursor)
    au FileType coq call coquille#FNMapping()

to your `.vimrc`.

Alternatively you can, of course, define your owns.

Running query commands
----------------------

You can run an arbitrary query command (that is `Check`, `Print`, etc.) by
calling `:Coq MyCommand foo bar baz` and the result will be displayed in the
Infos panel.

Screenshoots
------------

Because pictures are always the best sellers :

![Coquille at use](http://195.154.188.33/~rks/coquille.png)

[1]: https://github.com/tpope/vim-pathogen
[2]: https://github.com/def-lkb/vimbufsync
[3]: http://www.vim.org/scripts/script.php?script_id=2063 "coq syntax on vim.org"
[4]: http://www.vim.org/scripts/script.php?script_id=2079 "coq indent on vim.org"
