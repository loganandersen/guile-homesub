;; I wanted to make a homedir expansion similar to what you have in
;; bash.
;; https://www.gnu.org/software/bash/manual/html_node/Tilde-Expansion.html
;; The function I made basically works but it dosen't do directory
;; stack substitutions because that is very difficult to do. Bash
;; dosen't expose the directory stack to the user, so I'm pretty sure
;; it's not possible to do, but there could be a very ugly work
;; around. It also dosen't interperate backslashes or quotes. It does,
;; however work with OLDPWD (~-), PWD (~+) expansion.

(define-module (my-packages homesub))
(use-modules (ice-9 regex) (ice-9 match) (ice-9 exceptions))


;; tilde-prefix = ^~([^/])*
;; rest of path = .*$
;; full-regexp = ^(~[^/]*)?(.*)?$
;; path = tilde-prefix + rest of path ||

;; Note: The ^ and $ operators don't stand for start of line and end
;; of line, but rather start of string and end of string. See:
;; [[info:libc#Flags for POSIX Regexps][libc#Flags for POSIX Regexps]]
;; under REG_NEWLINE, it says Otherwise, newline acts like any other
;; ordinary character. in reference to ^ and $ if the flag isn't
;; active. [[info:guile#Regexp Functions][guile#Regexp Functions]]
;; states that regexes use the libc posix regexps, and that the
;; regexp/newline flag is off by default. So we don't have to worry
;; about filenames with newlines in them giving us trouble.
(define path-regexp (make-regexp "^(~[^/]*)?(.*)$"))
(define pwd-regexp (make-regexp "^(~\\+)(.*)$"))
(define old-pwd-regexp (make-regexp "^(~-)(.*)"))
(define remove-tilde-regexp (make-regexp "^(~)(.*)$"))

(define (split-with-regexp regexp string)
  "this takes a regexp of the form '^(first)(rest)$' and returns 
(first . rest) as a dotted pair, it returns #f if there's no match"
    (let ((mat (regexp-exec regexp string)))
      (if mat
	  (cons (match:substring mat 1) (match:substring mat 2))
	  mat)))

;; helper for the macro defined below.
(define-syntax let-cons-cond-helper
  (syntax-rules ()
    ;; base case
    ((let-cons-cond-helper car-name cdr-name (accumulated-statements ...) ()) 
     (let ((car-name #f)
	   (cdr-name #f)) ;; lexically scope the name 
       (cond accumulated-statements ...)))
    ;; recursive case
    ((let-cons-cond-helper car-name cdr-name (accumulated-statements ...) ((test expr ... ) other-expressions ...)) 
     (let-cons-cond-helper
      car-name cdr-name
      (accumulated-statements ...
			      ((let ((test-result test))
				 ;; A pair will always test as true, so we don't have to
				 ;; worry about cdr-name being assigned by a previous statement.
				 (if (pair? test-result) ;; conditionally set the results
				     (begin (set! car-name (car test-result))
					    (set! cdr-name (cdr test-result)))
				     (set! car-name test-result))
				 test-result) expr ...)) ;; add to accumulator
      (other-expressions ...))))) ;; remove the text-expr from from other expressions

;; This seems like a such a specific macro that I'm not going to use
;; it anywhere else. So I will keep it in this file. This macro is
;; useful when combined with split-regexp. It may have been better to
;; use cons with the => prefix honestly instead.
(define-syntax let-cons-cond
  (syntax-rules ()
    "(let-cons-cond car-name cdr-name statements ...)
let-cons-cond takes two names, and a series of cond statments in the
form (test expr ...). The result from the test will be saved to
car-name and cdr-name under the following conditions: If the result
returned from the test is not a pair, it assigns it to car-name (and
cdr-name is assigned to #f), if the result from test is a pair, then
it the car of the pair is assigned to car-name, and the cdr to cdr-name

Example call:
(let-cons-cond front back (#f ) ((= 2 3) front) ('(1 . 3) (+ front back)) (1 front))
=> 4
;; since back is #f if it's not a pair.
(let-cons-cond front back (#f ) (3 (cons front back)))
=> (3 . #f)"
    ((let-cons-cond car-name cdr-name test-expressions ...)
     (let-cons-cond-helper car-name cdr-name () (test-expressions ...)))))

;; (define pwd-regexp (make-regexp "^(~\\+)(.*)$"))
;; (define old-pwd-regexp (make-regexp "^(~-)(.*)"))
;; (define remove-tilde-regexp (make-regexp "^(~)(.*)$"))

;; It may have been better to just use cond => with a constructor
;; function instead of let-cons-cond.
;; [[info:guile#User Information][guile#User Information]] for getpwnam
(define (substitute-tilde tilde-prefix)
  "Expand the tilde in a tilde prefix according to a subset of bash rules.
Specifically, if the tilde has a name after it, look up the user in
the passwd file, if the tilde has a - do $OLDPWD, if the tilde has a
+, do $PWD, and if the tilde is alone do $HOME, and if there is no
$HOME, then look in the password file instead. If any of the varibles
aren't here then just return the previous prefix. "
  (let ((check-regexp
	 (lambda (regexp)
	   (split-with-regexp regexp tilde-prefix)))
	(env-test (lambda (environment-variable other-part)
		    (if (string-null? other-part)
			(let ((test (getenv environment-variable)))
			  (if test 
			      test
			      tilde-prefix))))))
    ;; actual logic begins here...
    (let-cons-cond
     tilde-part other-part
     ((not tilde-prefix) "") ;; if tilde-prefix is false, return empty string
     ((check-regexp old-pwd-regexp) ;; old-pwd-regexp rule
      (env-test (getenv "OLDPWD") other-part))
     ((check-regexp pwd-regexp) ;; pwd-regexp rule
      (env-test (getenv "PWD") other-part))
     ((check-regexp remove-tilde-regexp) ;; ~ and ~name rule.
      (with-exception-handler (lambda (exception)
				;; if origin of the error is from a
				;; call to getpw (or getpwnam), then
				;; return the tilde prefix,
				;; otherwise, re-raise the error.
				(if (and (exception-with-origin? exception)
					 (string=? (exception-origin exception) "getpw"))
				    tilde-prefix
				    (raise-exception exception)))
	(lambda ()
	  (if (string-null? other-part)
	      ;; if it is a lone tilde
	      (let ((home (getenv "HOME")))
		;; if getenv home worked
		(if home
		    home
		    ;; if it didn't work try to get users directory
		    ;; from the password file
		    (passwd:dir (getpwnam (getlogin)))))
	      ;; if it is not a lone tilde then the other part is
	      ;; the username we need to look up.
	      (passwd:dir (getpwnam other-part))))
	#:unwind? #t)))))





(define-public (homesub str)
  "Homesub takes a string and does bash tilde expansion on it.
It can do ~+ expansion ~name expanstion, ~- expansion, and ~/
expansion. It dosen't do directory stack expansion, and it dosen't to
backslash escaping on the home field."
  ;; path pair matches with every string.
  (let* ((path-pair (split-with-regexp path-regexp str))
	 (tilde-part (car path-pair))
	 (path-part (cdr path-pair)))
    (string-append (substitute-tilde tilde-part) path-part)))
