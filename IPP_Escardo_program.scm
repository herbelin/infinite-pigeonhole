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
      (@ coiter (lambda (pat) (match pat
                                 ((ExistT depth0 _) depth0))) (lambda (pat)
        (match pat
           ((ExistT depth0 rest0)
             (match (@ bool_dec (head rest0) b0)
                ((True) `(ExistT ,`(S ,depth0) ,(tail rest0)))
                ((False)
                  (callcc (lambda (restart)
                    (@ throw start
                      (@ coiter projT1 (lambda (pat0)
                        (match pat0
                           ((ExistT depth1 rest1)
                             (match (@ bool_dec (head rest1) b0)
                                ((True)
                                  (@ throw restart `(ExistT ,`(S ,depth1)
                                    ,(tail rest1))))
                                ((False) `(ExistT ,`(S ,depth1)
                                  ,(tail rest1))))))) `(ExistT ,`(S ,depth0)
                        ,(tail rest0))))))))))) `(ExistT ,`(O) ,(tail bs))))))))

(define take_ipp (lambdas (s n)
  (match n
     ((O) `(Nil))
     ((S n~)
       (match n~
          ((O) `(Cons ,(depth s) ,`(Nil)))
          ((S _) `(Cons ,(depth s) ,(@ take_ipp (@ rest s `(Tt)) n~))))))))
  
(define wrap (lambda (f) (f '(Tt))))

(define test (lambdas (n s)
  (wrap (lambda (_) (@ take_ipp (infinite_bool s) n)))))

(define always_true (delay `(Build_stream ,`(True) ,always_true)))
  
(define always_false (delay `(Build_stream ,`(False) ,always_false)))
  
(define test_stream (delay `(Build_stream ,`(True) (Build_stream ,`(False)
  (Build_stream ,`(True) (Build_stream ,`(False) (Build_stream ,`(True)
  (Build_stream ,`(True) (Build_stream ,`(False) (Build_stream ,`(False)
  (Build_stream ,`(True) (Build_stream ,`(True) ,always_false))))))))))))

(define test1 (@ test `(S ,`(O)) test_stream))

(define test2 (@ test `(S ,`(S ,`(O))) test_stream))

(define test3 (@ test `(S ,`(S ,`(S ,`(O)))) test_stream))

(define test4 (@ test `(S ,`(S ,`(S ,`(S ,`(O))))) test_stream))

(define test5 (@ test `(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))) test_stream))

(define test6 (@ test `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O))))))) test_stream))

(define test7
  (@ test `(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(S ,`(O)))))))) test_stream))

(define prova1 (delay `(Build_stream ,`(True) (Build_stream ,`(True)
  (Build_stream ,`(False) (Build_stream ,`(False) ,prova1))))))
  
(define prova2 (delay `(Build_stream ,`(True) (Build_stream ,`(True)
  (Build_stream ,`(False) (Build_stream ,`(False) (Build_stream ,`(False)
  ,prova2)))))))
  
(define prova3 (delay `(Build_stream ,`(True) (Build_stream ,`(True)
  (Build_stream ,`(False) (Build_stream ,`(False) ,always_false))))))

(define prova4 (delay `(Build_stream ,`(True) (Build_stream ,`(True)
  (Build_stream ,`(False) (Build_stream ,`(False) ,always_true))))))

(define testprova1 (@ test `(S ,`(S ,`(O))) prova1))

(define testprova2 (@ test `(S ,`(S ,`(O))) prova2))

(define testprova3 (@ test `(S ,`(S ,`(O))) prova3))

(define testprova4 (@ test `(S ,`(S ,`(O))) prova4))

(define example_ET2 (delay `(Build_stream ,`(True) (Build_stream ,`(False)
  (Build_stream ,`(True) (Build_stream ,`(False) ,always_false))))))

(define example_EF2 (delay `(Build_stream ,`(False) (Build_stream ,`(True)
  (Build_stream ,`(False) (Build_stream ,`(True) ,always_true))))))

(define test_ET2 (@ test `(S ,`(S ,`(S ,`(S ,`(O))))) example_ET2))

(define test_EF2 (@ test `(S ,`(S ,`(S ,`(S ,`(O))))) example_EF2))

