(herald yes-or-no)

;;; This is a protocol allowing the initiator to ask a yes-or-no
;;; question and receive an answer from the answer server that
;;; controls the public encryption key ans-key.

;;; The idea is that the questioner provides two randomly chosen
;;; nonces, called y and n here.  To provide an affirmative answer,
;;; the answerer releases the first of these, y.  For a negative
;;; answer, the second one, n.

;;; The questioner *branches* depending on which of the two is
;;; received.  The answerer *branches* depending which answer needs to
;;; be sent.

;;; Security property:  Even an adversary that *knows* what question
;;; will be asked on this occasion (or guesses it) learns nothing
;;; about what answer was given.  That's because all observations are
;;; invariant under reversing the order of the two nonces.  

(defprotocol yes-or-no basic
  (defrole init-positive
    (vars (y n data) (question text) (ans name) (ans-key akey))
    (trace
     (send (enc question y n ans-key))
     (recv y)))

  (defrole init-negative
    (vars (y n data) (question text) (ans name) (ans-key akey))
    (trace
     (send (enc question y n ans-key))
     (recv n)))

  (defrole resp-positive
    (vars (y n data) (question text) (ans name) (ans-key akey))
    (trace
     (recv (enc question y n ans-key))
     (send y)))

  (defrole resp-negative
    (vars (y n data) (question text) (ans name) (ans-key akey))
    (trace
     (recv (enc question y n ans-key))
     (send n))))

(defskeleton yes-or-no
  (vars (y data) (ans-key akey))
  (defstrand init-positive 2 (y y) (ans-key ans-key))
  (uniq-orig y)
  (non-orig (invk ans-key)))

(defskeleton yes-or-no
  (vars (ans-key akey) (n data))
  (defstrand init-negative 2 (n n) (ans-key ans-key))
  (uniq-orig n) 
  (non-orig (invk ans-key)))

(defskeleton yes-or-no
  (vars (y data) (ans-key akey))
  (defstrand init-positive 1 (y y) (ans-key ans-key))
  (deflistener y)
  (uniq-orig y)
  (non-orig (invk ans-key)))

(defskeleton yes-or-no
  (vars (n data) (ans-key akey))
  (defstrand init-positive 1 (n n) (ans-key ans-key))
  (deflistener n) 
  (uniq-orig n)
  (non-orig (invk ans-key)))
