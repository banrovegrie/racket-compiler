#lang racket
(require "priority_queue.rkt")
(require "heap.rkt")
(define pq (make-pqueue <))
(define h1 (pqueue-push! pq 1))
(define h2 (pqueue-push! pq 2))
(define h3 (pqueue-push! pq 1))
(define h4 (pqueue-push! pq 2))
(define h5 (pqueue-push! pq 3))
(define h6 (pqueue-push! pq 1))
(define h7 (pqueue-push! pq 5))
(set-node-key! h7 0)
(pqueue-decrease-key! pq h7)
(set-node-key! h5 0)
(pqueue-decrease-key! pq h5)
(set-node-key! h3 -1)
(pqueue-decrease-key! pq h3)
(define top (pqueue-pop! pq))
(define top2 (pqueue-pop! pq))
(define top3 (pqueue-pop! pq))
(define top4 (pqueue-pop! pq))
top
top2
top3
top4
