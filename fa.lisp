(defpackage finite-automata
  (:use :cl))

(in-package :finite-automata)

;; https://github.com/natefusion/donuts/
(ql:quickload "donuts")

(defmacro if-let ((var val) then &optional else)
  `(let ((,var ,val))
     (if ,var ,then ,else)))

(defun lexer (exp)
  (loop for x across exp
        append (cond ((alphanumericp x)
                      (list (read-from-string (string x))))
                     (t
                      (case x
                        ((#\+) '(union))
                        ((#\*) '(star))
                        ((#\# #\ℇ) '(empty))
                        ((#\.) '(dot))
                        ((#\-) '(-))
                        ((#\() '(|(|))
                        ((#\)) '(|)|))
                        ((#\space))
                        ((#\tab))
                        (t (error "wot in tarnation is '~a' doing here" x)))))))

(defun notate (exp)
  (labels ((infix-binding-power (op)
             (case op
               (union (values 1 2))
               (|)| (values nil nil '|)|))
               (t (values 3 4 'cat))))
           (postfix-binding-power (op)
             (case op
               (star 10)
               (t nil)))
           (infix->prefix (min-bp)
             (loop with lhs = (let ((lhs (pop exp)))
                                (case lhs
                                  (|(| (prog1 (infix->prefix 0)
                                         (unless (eq (pop exp) '|)|)
                                           (error "No closing parenthesis somewhere lol"))))
                                  ((cat) (list lhs (infix->prefix lhs)))
                                  (t lhs)))
                   for op = (car exp)
                   do (unless op (loop-finish))
                      (block thing
                        (if-let (lhs-bp (postfix-binding-power op))
                          (progn
                            (when (< lhs-bp min-bp)
                              (loop-finish))
                            (pop exp)
                            (setf lhs (list op lhs))
                            (return-from thing)))
                        (multiple-value-bind (lhs-bp rhs-bp special) (infix-binding-power op)
                          (cond ((or (eq special '|)|) (< lhs-bp min-bp))
                                 (loop-finish))
                                ((eq special 'cat)
                                 (setf op 'cat))
                                (t
                                 (pop exp)))
                          (setf lhs (list op lhs (infix->prefix rhs-bp)))))
                   finally (return lhs))))
    (setf exp (lexer exp))
    (infix->prefix 0)))

(defun traverse-regexp (regexp vertex)
  (declare (optimize (debug 3) (safety 3)))
  (cond ((atom regexp)
         (let ((accept-state (gensym "sym")))
           (values (list (list vertex (list regexp accept-state)))
                   (list accept-state))))
        ((listp regexp)
         (case (first regexp)
           (union (let ((lhs-vertex (gensym "+lhs"))
                        (rhs-vertex (gensym "+rhs")))
                    (multiple-value-bind (lhs lhs-accept-state) (traverse-regexp (second regexp) lhs-vertex)
                      (multiple-value-bind (rhs rhs-accept-state) (traverse-regexp (third regexp) rhs-vertex)
                        (values (append lhs rhs (list (list vertex (cons 'empty (list lhs-vertex rhs-vertex)))))
                                (append lhs-accept-state rhs-accept-state))))))
           (cat (let ((rhs-vertex (gensym "rhs")))
                  (multiple-value-bind (lhs lhs-accept-state) (traverse-regexp (second regexp) vertex)
                    (multiple-value-bind (rhs rhs-accept-state) (traverse-regexp (third regexp) rhs-vertex)
                      (values (append lhs rhs (loop for accept in lhs-accept-state collect (list accept (list 'empty rhs-vertex))))
                              rhs-accept-state)))))
           (star (let ((indirection-vertex (gensym "*"))
                       (indirection2-vertex (gensym "2*")))
                   (multiple-value-bind (graph accept-state) (traverse-regexp (second regexp) indirection-vertex)
                     (values (append graph
                                     (list (list vertex (list 'empty indirection-vertex indirection2-vertex)))
                                     (loop for accept in accept-state collect (list accept (list 'empty indirection-vertex indirection2-vertex))))
                             (list indirection2-vertex)))))
           (otherwise (error "wut operation is this: ~a" (first regexp)))))))

(defun get-empty-closure (start-states graph)
  (declare (optimize (debug 3)))
  (loop with closure = (make-hash-table)
        with worklist = (copy-list start-states)
          initially (dolist (state start-states) (setf (gethash state closure) t))
        while worklist
        for empty-dests = (cdr (assoc 'empty (cdr (assoc (pop worklist) graph))))
        do (dolist (dest empty-dests)
             (unless (gethash dest closure)
               (setf (gethash dest closure) t)
               (push dest worklist)))
        finally (return (loop for state being the hash-keys of closure collect state))))

(defun execute-finite-automata (input accept-states graph &key (start-state 'start) debug-print)
  (declare (optimize (debug 3)))
  (loop with current-states = (get-empty-closure (list start-state) graph)
        for char across input
        for i from 0
        for symbol = (car (lexer (string char)))
        do (when debug-print (format t "input[~a]=~a, current-states ~A~%" i symbol current-states))
           (loop for s in current-states
                 append (get-empty-closure (cdr (assoc symbol (cdr (assoc s graph)))) graph) into next-states
                 finally (setf current-states (remove-duplicates next-states)))
        finally (return (if-let (final-states (intersection current-states accept-states))
                                (values t final-states)
                                (values nil final-states)))))

(defun crawl-graph (graph)
  (declare (optimize (debug 3)))
  (labels ((recur (vertex path)
             (loop with (edge . ends) = (cadr (assoc vertex graph))
                     initially (when edge (return (list (list* vertex path))))
                   for end in ends
                   append (recur end (list* vertex path)))))
    (loop for (vertex (edge . ends)) in graph
          append (recur vertex nil))))

(defun crawl-and-merge (graph)
  (declare (optimize (debug 3)))
  (let ((paths (mapcar #'reverse (crawl-graph graph))))
    (print paths)
    (loop for x = paths then (cdr x) while x
          with really-final = nil
          do (loop for other in (cdr x)
                   do (when (eq (caar x) (car other))
                        (let ((existing (assoc (caar x) really-final)))
                          (if (assoc (caar x) really-final)
                              (setf (cdr existing) (append (cdr existing) other))
                              (push (append (car x) other) really-final)))))
          finally (return (mapcar (lambda (x)
                                    (let ((first (first x)))
                                      (reverse (list* first (remove-duplicates (remove first x))))))
                                  really-final)))))

(defun optimize-graph (graph accept-states &key debug)
  (declare (optimize (debug 3)))
  (loop with paths = (crawl-graph graph)
        with new-graph = (copy-tree graph)
        with new-accept-states = (copy-tree accept-states)

        initially (when debug (print paths))

        for path in paths
        for reversed-path = (reverse path)
        for start = (first reversed-path)
        for start-next = (second reversed-path)
        for end = (first path)

        for (start-ends) = (cdr (assoc start new-graph))
        when (> (length path) 1)
          do (when start-ends (setf (cdr start-ends) (list* end (remove start-next (cdr start-ends)))))

        when (>= (length path) 3)
          do (let ((smol-path (rest (butlast path))))
               (setf new-graph (remove-if (lambda (x) (member (car x) smol-path)) new-graph)
                     new-accept-states (set-difference new-accept-states smol-path)))

        finally (setf new-accept-states (remove-if-not (lambda (x) (member x new-graph :key #'car)) new-accept-states))
                (return (values new-graph new-accept-states))))


(defun generate-donut-commands (graph accept-states)
  (declare (optimize (debug 3) (safety 3)))
  (loop with accept-state-style = (list :style :filled :fillcolor :lightblue)
        for (vertex . edges-and-ends) in graph
        for vertex-accepted = (member vertex accept-states)
        append (loop for (edge . ends) in edges-and-ends
                     append (loop for end in ends
                                  for end-accepted = (member end accept-states)
                                  collect (donuts:-> (apply #'donuts:<>2 (symbol-name vertex) (when vertex-accepted accept-state-style)) (apply #'donuts:<>2 (symbol-name end) (when end-accepted accept-state-style)) :label (format nil "~a" (if (eq 'empty edge) "ℇ" edge)))))
          into nodes-and-edges
        finally (return nodes-and-edges)))

(defun fa (input expr &key expr-is-graph-and-accept-states print-graph optimize)
  (declare (optimize (debug 3) (safety 3)))
  
  (flet ((execute (graph accept-states start-state label &optional regexp)
           (multiple-value-bind (accepted final-state) (execute-finite-automata input accept-states graph :debug-print print-graph :start-state start-state)
             (when print-graph
               (format t "accepted: ~a~%graph: ~a~%accept states: ~a~%final state: ~a~%parsed: ~a~%" accepted graph accept-states final-state regexp)
               (donuts:$ (:outfile "output.dot") (donuts:& (:label label) (apply #'donuts:&& (generate-donut-commands graph accept-states)))))
             accepted)))
    (if expr-is-graph-and-accept-states
        (destructuring-bind (graph accept-states start-state) expr
          (execute graph accept-states start-state ""))
        (multiple-value-bind (graph accept-states) (if optimize (apply #'optimize-graph (values-list (traverse-regexp (notate expr) 'start))) (traverse-regexp (notate expr) 'start))
          (execute graph accept-states 'start (substitute #\ℇ #\# expr) (notate expr))))))

(defparameter *decimal* "(-+#)(0+1+2+3+4+5+6+7+8+9)(0+1+2+3+4+5+6+7+8+9)*(.(0+1+2+3+4+5+6+7+8+9)*+#)")
(defparameter *decimal-test* "(-+#)(0+1)(0+1)*(.(0+1)*+#)")
