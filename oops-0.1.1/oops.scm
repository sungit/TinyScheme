; A port of Elk's OOPS package
;

(define void (string->symbol ""))

(define (void? x) (eq? x (string->symbol "")))

(define (print arg)
  (begin (write arg)
	 (newline)
	 void))

(define (print2 arg1 arg2)
  (begin (display arg1)
	 (write arg2)
	 (newline)
	 void))

(define (error-extended sym str)
  (error (string-append (symbol->string sym) " -- " str)))

(define (arg->string arg)
  (if (list? arg)
    (list->string arg)
    (symbol->string arg)))

(define (error-extended-one sym str arg)
  (error (string-append (symbol->string sym) " -- " str (arg->string arg))))

(define (error-extended-two sym str1 arg1 str2 arg2)
  (error (string-append (symbol->string sym) " -- " str1 (arg->string arg1)
			str2 (arg->string arg2))))

(define class-size 5)
(define instance-size 3)

;;; Classes and instances are represented as vectors.  The first
;;; two slots (tag and class-name) are common to classes and instances.

(define (tag v) (vector-ref v 0))
(define (set-tag! v t) (vector-set! v 0 t))

(define (class-name v) (vector-ref v 1))
(define (set-class-name! v n) (vector-set! v 1 n))

(define (class-instance-vars c) (vector-ref c 2))
(define (set-class-instance-vars! c v) (vector-set! c 2 v))

(define (class-env c) (vector-ref c 3))
(define (set-class-env! c e) (vector-set! c 3 e))

(define (class-super c) (vector-ref c 4))
(define (set-class-super! c s) (vector-set! c 4 s))

(define (instance-env i) (vector-ref i 2))
(define (set-instance-env! i e) (vector-set! i 2 e))

;;; Methods are bound in the class environment.

(define (method-known? method class)
  (eval `(defined? ',method) (class-env class)))

(define (lookup-method method class)
  (eval method (class-env class)))

(define (class? c)
  (and (vector? c) (= (vector-length c) class-size) (eq? (tag c) 'class)))

(define (check-class sym c)
  (if (not (class? c))
      (error-extended sym "argument is not a class")))

(define (instance? i)
  (and (vector? i) (= (vector-length i) instance-size)
       (eq? (tag i) 'instance)))

(define (check-instance sym i)
  (if (not (instance? i))
      (error-extended sym "argument is not an instance")))

;;; Evaluate `body' within the scope of instance `i'.

(define-macro (with-instance i . body)
  `(eval '(begin ,@body) (instance-env ,i)))

;;; Set a variable in an instance.

(define (instance-set! instance var val)
  (eval `(set! ,var ',val) (instance-env instance)))

;;; Set a class variable when no instance is available.

(define (class-set! class var val)
  (eval `(set! ,var ',val) (class-env class)))

;;; Convert a class variable spec into a binding suitable for a `let'.

(define (make-binding var)
  (if (symbol? var)
      (list var '())   ; No initializer given; use ()
      var))            ; Initializer has been specified; leave alone

;;; Check whether the elements of `vars' are either a symbol or
;;; of the form (symbol initializer).

(define (check-vars vars)
  (if (not (null? vars))
      (if (not (or (symbol? (car vars))
		   (and (pair? (car vars)) (= (length (car vars)) 2)
			(symbol? (caar vars)))))
	  (error-extended-one 'define-class "bad variable spec: " (car vars))
	  (check-vars (cdr vars)))))

;;; Check whether the class var spec `v' is already a member of
;;; the list `l'.  If this is the case, check whether the initializers
;;; are identical.

(define (find-matching-var l v)
  (cond
   ((null? l) #f)
   ((eq? (caar l) (car v))
    (if (not (equal? (cdar l) (cdr v)))
	(error-extended-two 'define-class "initializer mismatch: "
	       (car l) " and " v)
	#t))
   (else (find-matching-var (cdr l) v))))

;;; Same as above, but don't check initializer.

(define (find-var l v)
  (cond
   ((null? l) #f)
   ((eq? (caar l) (car v)) #t)
   (else (find-var (cdr l) v))))

;;; Create a new list of class var specs by discarding all variables
;;; from `b' that are already a member of `a' (with identical initializers).

(define (join-vars a b)
  (cond
   ((null? b) a)
   ((find-matching-var a (car b)) (join-vars a (cdr b)))
   (else (join-vars (cons (car b) a) (cdr b)))))

;;; The syntax is as follows:
;;; (define-class class-name . options)
;;; options are: (super-class class-name)
;;;              (class-vars . var-specs)
;;;              (instance-vars . var-specs)
;;; each var-spec is either a symbol or (symbol initializer).

(define-macro (define-class name . args)
  (let ((class-vars) (instance-vars (list (make-binding 'self)))
	(super) (super-class-env))
    (do ((a args (cdr a))) ((null? a))
      (cond
       ((not (pair? (car a)))
	(error-extended-one 'define-class "bad argument: " (car a)))
       ((eq? (caar a) 'class-vars)
	(check-vars (cdar a))
	(set! class-vars (cdar a)))
       ((eq? (caar a) 'instance-vars)
	(check-vars (cdar a))
	(set! instance-vars (append instance-vars
				    (map make-binding (cdar a)))))
       ((eq? (caar a) 'super-class)
	(if (> (length (cdar a)) 1)
	    (error-extended 'define-class "only one super-class allowed"))
	(set! super (cadar a)))
       (else
	(error-extended-one 'define-class "bad keyword: " (caar a)))))
    (if (not (null? super))
	(let ((class (eval super)))
	  (set! super-class-env (class-env class))
	  (set! instance-vars (join-vars (class-instance-vars class)
				         instance-vars)))
	(set! super-class-env (current-environment)))
    `(define ,name
      (let ((c (make-vector class-size '())))
	(set-tag! c 'class)
	(set-class-name! c ',name)
	(set-class-instance-vars! c ',instance-vars)
	(set-class-env! c (eval `(let* ,(map make-binding ',class-vars)
				   (current-environment))
				,super-class-env))
	(set-class-super! c ',super)
	c))))

(define-macro (define-method class lambda-list . body)
  (if (not (pair? lambda-list))
      (error-extended 'define-method "bad lambda list"))
  `(begin
     (check-class 'define-method ,class)
     (let ((env (class-env ,class))
	   (method (car ',lambda-list))
	   (args (cdr ',lambda-list))
	   (forms ',body))
       (eval `(define ,method (lambda ,args ,@forms)) env)
       void)))

;;; All arguments of the form (instance-var init-value) are used
;;; to initialize the specified instance variable; then an
;;; initialize-instance message is sent with all remaining
;;; arguments.

(define-macro (make-instance class . args)
  `(begin
     (check-class 'make-instance ,class)
     (let* ((e (current-environment))
	    (i (make-vector instance-size #f))
	    (class-env (class-env ,class))
	    (instance-vars (class-instance-vars ,class)))
       (set-tag! i 'instance)
       (set-class-name! i ',class)
       (set-instance-env! i (eval `(let* ,instance-vars (current-environment))
				  class-env))
       (eval `(set! self ',i) (instance-env i))
       (init-instance ',args ,class i e)
       i)))

(define (init-instance args class instance env)
  (let ((other-args))
    (do ((a args (cdr a))) ((null? a))
      (if (and (pair? (car a)) (= (length (car a)) 2)
	       (find-var (class-instance-vars class) (car a)))
	  (instance-set! instance (caar a) (eval (cadar a) env))
	  (set! other-args (cons (eval (car a) env) other-args))))
    (call-init-methods class instance (if (not (null? other-args))
					(reverse other-args)))))

;;; Call all initialize-instance methods in super-class to sub-class
;;; order in the environment of `instance' with arguments `args'.

(define (call-init-methods class instance args)
  (let ((called '()))
    (let loop ((class class))
      (if (not (null? (class-super class)))
	  (loop (eval (class-super class))))
	  (if (method-known? 'initialize-instance class)
	      (let ((method (lookup-method 'initialize-instance class)))
		(if (not (memq method called))
		    (begin
		      (apply (set-closure-environment!
			      method (instance-env instance))
			     args)
		      (set! called (cons method called)))))))))

(define (send instance msg . args)
  (check-instance 'send instance)
  (let ((class (eval (class-name instance))))
    (if (not (method-known? msg class))
	(error-extended-one 'send "message not understood: " `(,msg ,@args))
	(apply (set-closure-environment! (lookup-method msg class)
					    (instance-env instance))
	       args))))

;;; If the message is not understood, return #f.  Otherwise return
;;; a list of one element, the result of the method.

(define (send-if-handles instance msg . args)
  (check-instance 'send-if-handles instance)
  (let ((class (eval (class-name instance))))
    (if (not (method-known? msg class))
	#f
	(list (apply (set-closure-environment! (lookup-method msg class)
						  (instance-env instance))
		     args)))))

(define (describe-class c)
  (check-class 'describe-class c)
  (print2 "Class name:         " (class-name c))
  (if (not (null? (class-super c)))
    (print2 "Superclass:         " (class-super c)))
  (display "Instancevars:       ")
  (do ((v (class-instance-vars c) (cdr v)) (space #f #t)) ((null? v))
      (if space
	  (display "                    "))
      (print (cons (caar v) (cadar v))))
  (display "Classvars/Methods:  ")
  (define v (car (environment->list (class-env c))))
  (if (not (null? v))
      (do ((f v (cdr f)) (space #f #t)) ((null? f))
	(if space
	    (display "                    "))
	(print (car f)))
      (print 'None))
      void)

(define (describe-instance i)
  (check-instance 'describe-instance i)
  (print2 "Instance of:   " (class-name i))
  (display "Instancevars:  ")
  (do ((f (car (environment->list (instance-env i))) (cdr f))
       (space #f #t)) ((null? f))
    (if space
	(display "               "))
    (print (car f)))
  void)
