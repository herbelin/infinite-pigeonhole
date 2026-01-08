;; This extracted scheme code relies on some additional macros
;; available at http://www.pps.univ-paris-diderot.fr/~letouzey/scheme
(load "macros_extr.scm")

(define __ (lambda (_) __))


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

(define coiter (lambdas (base next s) (delay `(Build_ipp_stream
  ,(@ base __ s) ,(lambda (_) (@ coiter base next (@ next __ s)))))))
  
(define bool_dec~ (lambdas (b b~)
  (match b
     ((True) (match b~
                ((True) `(Left))
                ((False) `(Right))))
     ((False) (match b~
                 ((True) `(Right))
                 ((False) `(Left)))))))

(define infinite_bool (lambda (bs)
  (let ((b0 (head bs)))
    (callcc (lambda (start)
      (@ coiter (lambdas (_ pat) (match pat
                                    ((ExistT depth0 _) depth0))) (lambdas (_
        pat)
        (match pat
           ((ExistT depth0 rest0)
             (match (@ bool_dec~ (head rest0) b0)
                ((Left) `(ExistT ,`(S ,depth0) ,(tail rest0)))
                ((Right)
                  (callcc (lambda (restart)
                    (@ throw start
                      (@ coiter (lambda (_) projT1) (lambdas (_ pat0)
                        (match pat0
                           ((ExistT depth1 rest1)
                             (match (@ bool_dec~ (head rest1) b0)
                                ((Left)
                                  (@ throw restart `(ExistT ,`(S ,depth1)
                                    ,(tail rest1))))
                                ((Right) `(ExistT ,`(S ,depth1)
                                  ,(tail rest1))))))) `(ExistT ,`(S ,depth0)
                        ,(tail rest0))))))))))) `(ExistT ,`(O) ,(tail bs))))))))

(define ipp_stream_depths (lambdas (bs k _ ms)
  (match k
     ((O) `(Nil))
     ((S k~)
       (match k~
          ((O) `(Cons ,(depth ms) ,`(Nil)))
          ((S _)
            (let ((d (depth ms)))
              (let ((ms~ (@ rest ms `(Tt))))
                `(Cons ,d ,(@ ipp_stream_depths bs k~ `(Some ,d) ms~))))))))))
  
(define take_ipp (lambdas (bs ms n) (@ ipp_stream_depths bs n `(None) ms)))

(define wrap (lambda (f) (f '(Tt))))

(define always_false (delay `(Build_stream ,`(False) ,always_false)))
  
(define test_stream (delay `(Build_stream ,`(True) (Build_stream ,`(False)
  (Build_stream ,`(True) (Build_stream ,`(False) (Build_stream ,`(True)
  (Build_stream ,`(True) (Build_stream ,`(False) (Build_stream ,`(False)
  (Build_stream ,`(True) (Build_stream ,`(True) ,always_false))))))))))))

(define test1
  (wrap (lambda (_)
    (@ take_ipp test_stream (infinite_bool test_stream) `(S ,`(O))))))

(define test2
  (wrap (lambda (_)
    (@ take_ipp test_stream (infinite_bool test_stream) `(S ,`(S ,`(O)))))))

(define test3
  (wrap (lambda (_)
    (@ take_ipp test_stream (infinite_bool test_stream) `(S ,`(S ,`(S
      ,`(O))))))))

(define test4
  (wrap (lambda (_)
    (@ take_ipp test_stream (infinite_bool test_stream) `(S ,`(S ,`(S ,`(S
      ,`(O)))))))))

(define test5
  (wrap (lambda (_)
    (@ take_ipp test_stream (infinite_bool test_stream) `(S ,`(S ,`(S ,`(S
      ,`(S ,`(O))))))))))

(define test6
  (wrap (lambda (_)
    (@ take_ipp test_stream (infinite_bool test_stream) `(S ,`(S ,`(S ,`(S
      ,`(S ,`(S ,`(O)))))))))))

(define test7
  (wrap (lambda (_)
    (@ take_ipp test_stream (infinite_bool test_stream) `(S ,`(S ,`(S ,`(S
      ,`(S ,`(S ,`(S ,`(O))))))))))))

