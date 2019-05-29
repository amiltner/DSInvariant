(define-sort IList () (List Int))
(declare-rel lookup (IList Int))
(declare-rel delete (IList Int IList))
(declare-rel searchlist! (Int IList))
(declare-rel searchlist (IList))
(declare-var l IList)
(declare-var l! IList)
(declare-var t IList)
(declare-var h Int)
(declare-var x Int)

(rule (lookup (insert h t) h))
(rule (=> (and (> x h) (lookup t x)) (lookup (insert h t) x)))

(rule (delete nil x nil))
(rule (delete (insert x t) x t))
(rule (=> (< x h) (delete (insert h t) x (insert h t))))
(rule (=> (and (> x h) (delete t x l)) (delete (insert h t) x (insert h l))))

(rule (searchlist! x nil))
(rule (=> (and (< x h) (searchlist! h t)) (searchlist! x (insert h t))))

(rule (searchlist nil))
(rule (=> (searchlist! h t) (searchlist (insert h t))))

(declare-rel fail ())
(rule (=> (and (searchlist l) (delete l x l!) (lookup l! x)) fail))

(query fail)