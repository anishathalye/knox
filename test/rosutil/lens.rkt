#lang rosette/safe

(require rosutil rackunit
         (only-in racket/base symbol->string)
         racket/match)

(test-case "basic"
  (define tree '((a . b) c . d))
  (define cdar-lens (lens-compose cdr-lens car-lens))
  (check-equal? (lens-view cdar-lens tree) 'b)
  (check-equal? (lens-set cdar-lens tree 'x) '((a . x) c . d))
  (check-equal? (lens-transform cdar-lens tree symbol->string) '((a . "b") c . d)))

(test-case "symbolic"
  (define-symbolic* b boolean?)
  (define-symbolic* w x y z integer?)
  (define t (if b (cons w x) (cons y z)))
  (check-pred unsat? (verify (assert (equal? (lens-view car-lens t) (if b w y)))))
  (check-pred unsat? (verify (assert (equal? (lens-transform cdr-lens t add1) (if b (cons w (add1 x)) (cons y (add1 z)))))))
  (check-pred unsat? (verify (assert (equal? (lens-set cdr-lens t 3) (cons (if b w y) 3))))))

(test-case "union"
  (define-symbolic* b boolean?)
  (define obj (if b '((a . b) c . d) '((w . x) y . z)))
  (define cdar-lens (lens-compose cdr-lens car-lens))
  (check-pred unsat? (verify (assert (equal? (lens-view cdar-lens obj) (if b 'b 'x))))))

(test-case "thrush"
  (define obj '((1 2) (3) (4 (5 (6 7 8)))))
  (define l (lens-thrush (list-ref-lens 2)
                         cdr-lens
                         car-lens
                         cdr-lens
                         car-lens
                         (list-ref-lens 1)))
  (check-equal? (lens-view l obj) 7)
  (check-equal? (lens-transform l obj (lambda (n) (* n 2))) '((1 2) (3) (4 (5 (6 14 8))))))

(test-case "join"
  (define obj '((1 2) (3) (4 (5 (6 7 8)))))
  (define l (lens-join (list-ref-lens 0)
                       (lens-thrush
                        (list-ref-lens 2)
                        car-lens)))
  (check-equal? (lens-view l obj) (join '((1 2) 4)))
  (check-equal? (lens-set l obj (join '(a b))) '(a (3) (b (5 (6 7 8)))))
  (check-equal? (lens-transform l obj (lambda (j)
                                        (let ([prev (join-contents j)])
                                          (join* (second (first prev)) (+ (first (first prev)) (second prev))))))
                '(2 (3) (5 (5 (6 7 8))))))

(test-case "list"
  (define obj '((1 2) 3 (4 5) (6 (7))))
  (define l (lens-thrush (list-ref-lens 3) (list-ref-lens 1) (list-ref-lens 0)))
  (check-equal? (lens-view l obj) 7)
  (check-equal? (lens-set l obj 8) '((1 2) 3 (4 5) (6 (8))))
  (check-equal? (lens-transform l obj sub1) '((1 2) 3 (4 5) (6 (6)))))

(test-case "vector"
  (define l (lens-compose car-lens (vector-ref-lens 3)))
  (define v '#(0 1 2 (3 . 4)))
  (check-equal? (lens-view l v) 3)
  (check-equal? (lens-set l v 8) '#(0 1 2 (8 . 4))))

(test-case "struct"
  (addressable-struct a (b c))
  (addressable-struct d (e f))
  (define obj (a (list 0 (d 1 2)) 3))
  (define l (lens-thrush (struct-ref-lens 'b) (list-ref-lens 1) (struct-ref-lens 'e)))
  (check-equal? (lens-view l obj) 1)
  (check-equal? (lens-set l obj 4) (a (list 0 (d 4 2)) 3))
  (check-equal? (lens-transform l obj sub1) (a (list 0 (d 0 2)) 3)))

(test-case "struct join"
  (addressable-struct a (b c d))
  (define obj (a 1 2 3))
  (define l (lens-join (struct-ref-lens 'b) (struct-ref-lens 'c)))
  (check-equal? (lens-view l obj) (join '(1 2)))
  (check-equal? (lens-set l obj (join '(-1 -2))) (a -1 -2 3))
  (check-equal? (lens-transform l obj (lambda (j) (let ([l (join-contents j)]) (join* (second l) (first l))))) (a 2 1 3)))

(test-case "struct filter"
  (addressable-struct a (uart_div uart_baud cycle_count))
  (define obj (a 0 1 2))
  (define l (struct-filter-lens #rx"^uart.*$"))
  (check-equal? (lens-view l obj) (join '(0 1)))
  (check-equal? (lens-set l obj (join '(10 11))) (a 10 11 2))
  (check-equal? (lens-transform l obj (lambda (j) (let ([l (join-contents j)]) (join* (second l) (first l))))) (a 1 0 2)))

(test-case "vector join"
  (define obj #(#(0 1 2) #(3 #(4 5))))
  (define l (lens (list (lens 0 (list 0 1)) (lens 1 0))))
  (check-equal? (lens-view l obj) (join* (join* 0 1) 3))
  (check-equal? (lens-set l obj (join* (join* 10 11) 13)) #(#(10 11 2) #(13 #(4 5))))
  (check-equal? (lens-transform l obj (lambda (j) (let ([lst (join-contents j)]) (join* (first lst) (add1 (second lst))))))
                #(#(0 1 2) #(4 #(4 5)))))

(test-case "struct join"
  (addressable-struct foo (a b c d e))
  (define obj (foo 1 2 3 4 #(5 6)))
  (define l (lens (list 'a 'b 'd (lens 'e 1))))
  (check-equal? (lens-view l obj) (join* 1 2 4 6))
  (check-equal? (lens-set l obj (join* 1 3 3 7)) (foo 1 3 3 3 #(5 7)))
  (check-equal? (lens-transform l obj (lambda (j) (let* ([l (join-contents j)] [s (apply + l)]) (join* s s s s))))
                (foo 13 13 3 13 #(5 13))))

(test-case "lens"
  (define obj '#(#(1 2) #(3) #(4 #(5 #(6 7 8)))))
  (define l (lens 2 1 (list 0 (lens 1 1))))
  (check-equal? (lens-view l obj) (join* 5 7))
  (check-equal? (lens-set l obj (join* 10 20)) '#(#(1 2) #(3) #(4 #(10 #(6 20 8))))))

(test-case "lens struct"
  (addressable-struct person (name location))
  (addressable-struct location (street city))
  (define obj (vector (person "Bob" (location "123 First Street" "Cambridge"))))
  (define l (lens 0 'location 'city))
  (check-equal? (lens-view l obj) "Cambridge")
  (check-equal? (lens-set l obj "Boston") (vector (person "Bob" (location "123 First Street" "Boston"))))
  (define l2 (lens 0 (list 'name (lens 'location 'street))))
  (check-equal? (lens-view l2 obj) (join* "Bob" "123 First Street"))
  (define l3 (lens 0 'location (list 'street 'city)))
  (check-equal? (lens-set l3 obj (join* "1 Main Street" "Shrewsbury")) (vector (person "Bob" (location "1 Main Street" "Shrewsbury")))))

(test-case "lens filter"
  (addressable-struct mod (uart_baud uart_div clk))
  (define obj (mod 1 2 3))
  (define l (lens #rx"uart_.*"))
  (check-equal? (lens-view l obj) (join* 1 2)))

(test-case "join efficiency"
  (define counter 0)
  (define (inc!) (set! counter (add1 counter)))
  (define (reset!) (set! counter 0))
  (define (get) counter)
  (struct s (a b c) #:transparent
    #:methods gen:addressable
    [(define (fields _) '(a b c))
     (define (get-field x f)
       ((case f [(a) s-a] [(b) s-b] [(c) s-c]) x))
     (define (map-fields x f)
       (inc!)
       (s (f 'a (s-a x))
          (f 'b (s-b x))
          (f 'c (s-c x))))])
  (define (inc-all j) (join (map add1 (join-contents j))))
  ;; two field-refs combined into one
  (define o1 (s 1 2 3))
  (define l1 (lens (list 'a 'b)))
  (check-equal? (lens-transform l1 o1 inc-all) (s 2 3 3))
  (check-equal? (get) 1)
  (reset!)
  ;; multiple field-refs, including nesting, combined into one
  (define o2 (s 1 2 '#(3 4)))
  (define l2 (lens (list 'a (lens 'c 0))))
  (check-equal? (lens-transform l2 o2 inc-all) (s 2 2 '#(4 4)))
  (check-equal? (get) 1)
  (reset!)
  ;; combining filter and individual refs
  (define o3 o2)
  (define l3 (lens (list #rx"^[ab]$" (lens 'c 1))))
  (check-equal? (lens-transform l3 o3 (match-lambda [(join (list (join (list a b)) c)) (join* (join* c b) a)]))
                (s 4 2 '#(3 1)))
  (check-equal? (get) 1)
  (reset!)
  ;; more nesting
  (define o4 (s 1 2 (s 3 4 5)))
  (define l4 (lens (list #rx"a" (lens 'c (list 'a 'b #rx"c")))))
  (check-equal? (lens-transform l4 o4 identity) o4)
  (check-equal? (get) 2)
  (reset!))

(test-case "overlapping field in join"
  ;; regression test
  (addressable-struct pair (circuit simulator))
  (addressable-struct simulator (auxiliary oracle))
  (define o (pair 0 (simulator 1 2)))
  (define l (lens (list (lens 'simulator 'auxiliary)
                        (lens 'simulator 'oracle))))
  ;; this lens is purposefully written in a weird way;
  ;; it should have been written as the following instead:
  (define l-ok (lens 'simulator (list 'auxiliary 'oracle)))
  (check-exn #rx"simulator" (lambda () (lens-set l o (join '(10 20)))))
  (check-equal? (lens-set l-ok o (join '(10 20))) (pair 0 (simulator 10 20))))

(test-case "virtual lens"
  (addressable-struct executor (interpreter pc equalities))
  (addressable-struct interpreter (globals control environment continuation))
  (addressable-struct globals (circuit meta))
  (define x (executor (interpreter (globals "ckt" "meta") "control" "environment" "continuation") "pc" "equalities"))
  (define top (virtual-lens (list
                             (cons 'circuit (lens 'interpreter 'globals 'circuit))
                             (cons 'interpreter (lens 'interpreter (virtual-lens (list
                                                                                  (cons 'control (lens 'control))
                                                                                  (cons 'environment (lens 'environment))
                                                                                  (cons 'continuation (lens 'continuation)))))))))
  (check-equal? (lens-view (lens top 'interpreter 'control) x) "control"))
