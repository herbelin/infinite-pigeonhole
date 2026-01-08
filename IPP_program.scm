;; This extracted scheme code relies on some additional macros
;; available at http://www.pps.univ-paris-diderot.fr/~letouzey/scheme
(load "macros_extr.scm")


(define projT1 (lambda (x) (match x
                              ((ExistT a _) a))))

(define callcc call/cc)

(define throw (lambda (x) x))

(define head (lambda (s) (match (force
                            s)
                            ((Build_stream head0 _) head0))))

(define tail (lambda (s) (match (force
                            s)
                            ((Build_stream _ tail0) tail0))))

(define depth (lambda (i)
  (match (force
     i)
     ((Build_ipp_stream depth0 _) depth0))))

(define rest (lambda (i)
  (match (force
     i)
     ((Build_ipp_stream _ rest0) rest0))))

(define coiter (lambdas (base next s) (delay `(Build_ipp_stream ,(base s)
  ,(lambda (_) (@ coiter base next (next s)))))))
  
(define corecM (lambdas (base next s) (delay `(Build_ipp_stream ,(base s)
  ,(lambda (_)
  (match (next s)
     ((Inl s0) s0)
     ((Inr x) (@ corecM base next x))))))))
  
(define corecC (lambdas (base next)
  (@ corecM base (lambda (s)
    (callcc (lambda (disjret) `(Inr
      ,(@ next s (lambda (ret) (disjret `(Inl ,ret)))))))))))

(define bool_dec (lambdas (b b~)
  (match b
     ((True) (match b~
                ((True) `(True))
                ((False) `(False))))
     ((False) (match b~
                 ((True) `(False))
                 ((False) `(True)))))))

(define infinite_bool (lambda (bs)
  (let ((b0 (head bs)))
    (callcc (lambda (start)
      (@ coiter (lambda (pat)
        (match pat
           ((ExistT x _) (match x
                            ((ExistT depth0 _) depth0))))) (lambda (pat)
        (match pat
           ((ExistT x switch)
             (match x
                ((ExistT depth0 rest0)
                  (match (@ bool_dec (head rest0) b0)
                     ((True) `(ExistT ,`(ExistT ,`(S ,depth0) ,(tail rest0))
                       ,switch))
                     ((False)
                       (callcc (lambda (restart)
                         (@ throw switch
                           (@ corecC projT1 (lambdas (pat0 ret)
                             (match pat0
                                ((ExistT depth1 rest1)
                                  (match (@ bool_dec (head rest1) b0)
                                     ((True)
                                       (@ throw restart `(ExistT ,`(ExistT
                                         ,`(S ,depth1) ,(tail rest1)) ,ret)))
                                     ((False) `(ExistT ,`(S ,depth1)
                                       ,(tail rest1))))))) `(ExistT ,`(S
                             ,depth0) ,(tail rest0))))))))))))) `(ExistT
        ,`(ExistT ,`(O) ,(tail bs)) ,start)))))))

(define take_ipp (lambdas (s n)
  (match n
     ((O) `(Nil))
     ((S n~) `(Cons ,(depth s) ,(@ take_ipp (@ rest s `(Tt)) n~))))))
  
(define wrap (lambda (f) (f '(Tt))))

(define always_true (delay `(Build_stream ,`(True) ,always_true)))
  
(define always_false (delay `(Build_stream ,`(False) ,always_false)))
  
(define test_stream (delay `(Build_stream ,`(True) (Build_stream ,`(False)
  (Build_stream ,`(True) (Build_stream ,`(False) (Build_stream ,`(True)
  (Build_stream ,`(True) (Build_stream ,`(False) (Build_stream ,`(False)
  (Build_stream ,`(True) (Build_stream ,`(True) ,always_false))))))))))))

(define test1
  (wrap (lambda (_) (@ take_ipp (infinite_bool test_stream) `(S ,`(O))))))

(define test2
  (wrap (lambda (_)
    (@ take_ipp (infinite_bool test_stream) `(S ,`(S ,`(O)))))))

(define test3
  (wrap (lambda (_)
    (@ take_ipp (infinite_bool test_stream) `(S ,`(S ,`(S ,`(O))))))))

(define test4
  (wrap (lambda (_)
    (@ take_ipp (infinite_bool test_stream) `(S ,`(S ,`(S ,`(S ,`(O)))))))))

(define test5
  (wrap (lambda (_)
    (@ take_ipp (infinite_bool test_stream) `(S ,`(S ,`(S ,`(S ,`(S
      ,`(O))))))))))

(define test6
  (wrap (lambda (_)
    (@ take_ipp (infinite_bool test_stream) `(S ,`(S ,`(S ,`(S ,`(S ,`(S
      ,`(O)))))))))))

(define test7
  (wrap (lambda (_)
    (@ take_ipp (infinite_bool test_stream) `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S
      ,`(O))))))))))))

(define prova1 (delay `(Build_stream ,`(True) (Build_stream ,`(True)
  (Build_stream ,`(False) (Build_stream ,`(False) ,prova1))))))
  
(define prova2 (delay `(Build_stream ,`(True) (Build_stream ,`(True)
  (Build_stream ,`(False) (Build_stream ,`(False) (Build_stream ,`(False)
  ,prova2)))))))
  
(define prova3 (delay `(Build_stream ,`(True) (Build_stream ,`(True)
  (Build_stream ,`(False) (Build_stream ,`(False) ,always_false))))))

(define prova4 (delay `(Build_stream ,`(True) (Build_stream ,`(True)
  (Build_stream ,`(False) (Build_stream ,`(False) ,always_true))))))

(define testprova1
  (wrap (lambda (_) (@ take_ipp (infinite_bool prova1) `(S ,`(S ,`(O)))))))

(define testprova2
  (wrap (lambda (_) (@ take_ipp (infinite_bool prova2) `(S ,`(S ,`(O)))))))

(define testprova3
  (wrap (lambda (_) (@ take_ipp (infinite_bool prova3) `(S ,`(S ,`(O)))))))

(define testprova4
  (wrap (lambda (_) (@ take_ipp (infinite_bool prova4) `(S ,`(S ,`(O)))))))

