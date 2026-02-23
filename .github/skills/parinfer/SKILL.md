---
name: parinfer
description: Check and correct parenthesis balance from indentation.
---
Check if installed
```bash
cd /workspace/acl2-jupyter && make test-parinfer
```

Install
```bash
cd /workspace/acl2-jupyter && make install-parinfer
```

Correct parens from indentation
```bash
. $HOME/.cargo/env && parinfer-rust -m indent -l lisp --lisp-block-comments <file.lisp | diff file.lisp -
```

Help
```bash
parinfer-rust --help
Usage: parinfer-rust [options]

Options:
        --comment-char CC
                        (default: ';')
        --string-delimiters DELIM
                        (default: '"')
    -h, --help          show this help message
        --input-format FMT
                        'json', 'text' (default: 'text')
        --guile-block-comments 
                        recognize #!/guile/block/comments \n!# )
        --no-guile-block-comments 
                        do not recognize #!/guile/block/comments \n!# )
        --hy-bracket-strings 
                        recognize #[hy-style[ bracket strings ]hy-style]```
        --no-hy-bracket-strings 
                        do not recognize #[hy-style[ bracket strings
                        ]hy-style]```
        --janet-long-strings 
                        recognize ``` janet-style long strings ```
        --no-janet-long-strings 
                        do not recognize ``` janet-style long strings ```
    -l, --language LANG 'clojure', 'guile', 'hy', 'janet', 'lisp', 'racket',
                        'scheme' (default: 'clojure')
        --lisp-block-comments 
                        recognize #| lisp-style block commments |#.
        --no-lisp-block-comments 
                        do not recognize #| lisp-style block commments |#.
        --lisp-vline-symbols 
                        recognize |lisp-style vline symbol|s.
        --no-lisp-vline-symbols 
                        do not recognize |lisp-style vline symbol|s.
    -m, --mode MODE     parinfer mode (indent, paren, or smart) (default:
                        smart)
        --output-format FMT
                        'json', 'kakoune', 'text' (default: 'text')
        --scheme-sexp-comments 
                        recognize #;( scheme sexp comments )
        --no-scheme-sexp-comments 
                        do not recognize #;( scheme sexp comments )
```
