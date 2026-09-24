(herald concurrent-yahalom
  (comment "A Survey of Authentication Protocol Literature:"
	   "Version 1.0, John Clark and Jeremy Jacob,"
	   "Yahalom Protocol, Section 6.3.6, Page 49,"
	   "altered by Joshua to allow maximum interleaving "
	   "between the peers"
	   "Observe that the server checks (not (= a b))")
  (url "http://www.eecs.umich.edu/acal/swerve/docs/49-1.pdf")
  (bound 15))

(defprotocol c-y basic
  (defrole init
    (vars (a b s name) (n-a n-b text) (k skey))
    (trace
     (send (cat a b n-a))
     (recv (enc a b k n-a n-b (ltk a s)))
     (send (enc "1" a b n-a n-b k))
     (recv (enc "2" a b n-a n-b k))))
  (defrole resp
    (vars (a b s name) (n-a n-b text) (k skey))
    (trace
     (send (cat a b n-b))
     (recv (enc a b k n-a n-b (ltk b s)))
     (send (enc "2" a b n-a n-b k))
     (recv (enc "1" a b n-a n-b k))))
  (defrole serv
    (vars (a b s name) (n-a n-b text) (k skey))
    (trace
     (recv (cat a b n-a))
     (recv (cat a b n-b))
     (send (enc a b k n-a n-b (ltk a s)))
     (send (enc a b k n-a n-b (ltk b s))))
    (uniq-orig k)
    (facts (neq a b)))
  (comment "Yahalom protocol, Section 6.3.6, Page 49")
  (url "http://www.eecs.umich.edu/acal/swerve/docs/49-1.pdf"))

(defskeleton c-y
  (vars (a b s name) (n-a n-b text))
  (defstrand init 4 (a a) (b b) (s s) (n-a n-a) (n-b n-b))
  (non-orig (ltk a s) (ltk b s))
  (uniq-orig n-a n-b))

(defskeleton c-y
  (vars (a b s name) (n-a n-b text) (k skey))
  (defstrand resp 4 (a a) (b b) (s s) (n-a n-a) (n-b n-b) (k k))
  (deflistener k)
  (non-orig (ltk a s) (ltk b s))
  (uniq-orig n-b))

(defskeleton c-y
  (vars (a b s name) (n-a n-b text))
  (defstrand resp 4 (a a) (b b) (s s) (n-a n-a) (n-b n-b))
  (non-orig (ltk a s) (ltk b s))
  (uniq-orig n-b))

(defskeleton c-y
  (vars (a b s name) (n-a n-b text))
  (defstrand serv 4 (a a) (b b) (s s) (n-a n-a) (n-b n-b))
  (non-orig (ltk a s) (ltk b s)))

(defskeleton c-y
  (vars (a b s name) (k skey) (n-a n-b text))
  (defstrand serv 4 (a a) (b b) (s s) (n-a n-a) (n-b n-b) (k k))
  (deflistener k)
  (non-orig (ltk a s) (ltk b s)))
