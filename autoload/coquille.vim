let s:coq_running=0
let s:current_dir=expand("<sfile>:p:h") 

" Load vimbufsync if not already done
call vimbufsync#init()

py import sys, vim
py if not vim.eval("s:current_dir") in sys.path:
\    sys.path.append(vim.eval("s:current_dir")) 
py import coquille

function! coquille#ShowPanels()
    " open the Goals & Infos panels before going back to the main window
    let l:winnb = winnr()
    rightbelow vnew Goals
        setlocal buftype=nofile
        setlocal noswapfile
        let s:goal_buf = bufnr("%")
    rightbelow new Infos
        setlocal buftype=nofile
        setlocal noswapfile
        let s:info_buf = bufnr("%")
    execute l:winnb . 'winc w'
endfunction

function! coquille#KillSession()
    let s:coq_running = 0

    execute 'bdelete' . s:goal_buf
    execute 'bdelete' . s:info_buf
    py coquille.kill_coqtop()

    setlocal ei=InsertEnter
endfunction

function! coquille#RawQuery(...)
    py coquille.coq_raw_query(*vim.eval("a:000"))
endfunction

function! coquille#FNMapping()
    "" --- Function keys bindings
    "" Works under all tested config.
    map <buffer> <silent> <F2> :CoqUndo<CR>
    map <buffer> <silent> <F3> :CoqNext<CR>
    map <buffer> <silent> <F4> :CoqToCursor<CR>

    imap <buffer> <silent> <F2> <ESC>:CoqUndo<CR>a
    imap <buffer> <silent> <F3> <ESC>:CoqNext<CR>a
    imap <buffer> <silent> <F4> <ESC>:CoqToCursor<CR>a
endfunction

function! coquille#CoqideMapping()
    "" ---  CoqIde key bindings
    "" Unreliable: doesn't work with all terminals, doesn't work through tmux,
    ""  etc.
    map <buffer> <silent> <C-A-Up>    :CoqUndo<CR>
    map <buffer> <silent> <C-A-Left>  :CoqToCursor<CR>
    map <buffer> <silent> <C-A-Down>  :CoqNext<CR>
    map <buffer> <silent> <C-A-Right> :CoqToCursor<CR>

    imap <buffer> <silent> <C-A-Up>    <ESC>:CoqUndo<CR>a
    imap <buffer> <silent> <C-A-Left>  <ESC>:CoqToCursor<CR>a
    imap <buffer> <silent> <C-A-Down>  <ESC>:CoqNext<CR>a
    imap <buffer> <silent> <C-A-Right> <ESC>:CoqToCursor<CR>a
endfunction

function! coquille#Launch(...)
    if s:coq_running == 1
        echo "Coq is already running"
    else
        let s:coq_running = 1

        " initialize the plugin (launch coqtop)
        py coquille.launch_coq(*vim.eval("a:000"))

        call coquille#ShowPanels()

        " make the different commands accessible
        command! -buffer CoqNext py coquille.coq_next()
        command! -buffer CoqUndo py coquille.coq_rewind()
        command! -buffer CoqToCursor py coquille.coq_to_cursor()
        command! -buffer CoqKill call coquille#KillSession()

        command! -buffer -nargs=* Coq call coquille#RawQuery(<f-args>)

        " Automatically sync the buffer when entering insert mode: this is usefull
        " when we edit the portion of the buffer which has already been sent to coq,
        " we can then rewind to the appropriate point.
        " It's still incomplete though, the plugin won't sync when you undo or
        " delete some part of your buffer. So the highlighting will be wrong, but
        " nothing really problematic will happen, as sync will be called the next
        " time you explicitly call a command (be it 'rewind' or 'interp')
        au InsertEnter <buffer> py coquille.sync()
    endif
endfunction

function! coquille#Register()
    hi CheckedByCoq ctermbg=17 guibg=LightGreen
    hi SentToCoq ctermbg=60 guibg=LimeGreen
    hi link CoqError Error

    let b:checked = -1
    let b:sent    = -1
    let b:errors  = -1

    command! -bar -buffer -nargs=* CoqLaunch call coquille#Launch(<f-args>)
endfunction
