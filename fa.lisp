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
                        ((#\#) '(nil))
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
                        (values (append lhs rhs (list (list vertex (cons nil (list lhs-vertex rhs-vertex))))) (append lhs-accept-state rhs-accept-state))))))
           (cat (let ((lhs-vertex (gensym "lhs")))
                  (multiple-value-bind (lhs lhs-accept-state) (traverse-regexp (second regexp) lhs-vertex)
                    (loop with graph = (append lhs (list (list vertex (cons nil (list lhs-vertex)))))
                          with accept-states = nil
                          for lhs-accept in lhs-accept-state
                          do (let ((indirection-vertex (gensym "2lhs")))
                               (multiple-value-bind (rhs rhs-accept-state) (traverse-regexp (third regexp) indirection-vertex)
                                 (setf graph (append rhs graph)
                                       accept-states (append (list lhs-accept) rhs-accept-state accept-states))
                                 (if-let (x (assoc lhs-accept graph))
                                   (setf (cdr x) (list (cons nil (list* indirection-vertex (cdadr x)))))
                                   (setf graph (append (list (list lhs-accept (cons nil (list indirection-vertex)))) graph)))))
                          finally (return (values graph accept-states))))))
           (star (let ((indirection-vertex (gensym "*"))
                       (indirection2-vertex (gensym "2*")))
                   (multiple-value-bind (graph accept-state) (traverse-regexp (second regexp) indirection-vertex)
                     (values (append graph (list (list vertex (cons nil (list indirection-vertex indirection2-vertex)))) (loop for accept in accept-state collect (list accept (list nil vertex))))
                             (list* indirection2-vertex  vertex accept-state)))))
           (otherwise (error "wut operation is this: ~a" (first regexp)))))
        ))

(defun execute-finite-automata (input accept-states graph &key (start-state 'start) debug-print)
  (declare (optimize (debug 3) (safety 3)))
  (labels ((debug-print (symbol branch custom)
             (when debug-print (format t "b~a ~a '~a'~%" branch custom symbol)))
           (crawl-empty-set-paths (idx current-state branch &optional symbol)
             (let ((empty-set-vertex (cdr (assoc nil (cdr (assoc current-state graph))))))
               (if (>= (length empty-set-vertex) 1)
                   (let ((cnt 0))
                     (dolist (v empty-set-vertex)
                       (multiple-value-bind (accepted state) (execute idx v (+ (* cnt 11) (1+ branch)))
                         (if accepted
                             (return (progn (debug-print symbol branch (list current-state "SUCCEED0")) (values t state))) ))
                       (incf cnt)))
                   nil)))
           (execute (start-idx current-state branch)
             (loop for idx from start-idx below (length input)
                   for symbol = (car (lexer (string (char input idx))))
                   do (debug-print symbol branch current-state)
                      (multiple-value-bind (accepted state) (crawl-empty-set-paths idx current-state branch symbol)
                        (when accepted (return (values accepted state))))
                      (if-let (vertex (cadr (assoc symbol (cdr (assoc current-state graph)))))
                        (setf current-state vertex)
                        (return (progn (debug-print symbol branch (list current-state "FAIL(CANNOT CONTINUE)")) (values nil current-state))))
                   finally
                      (return (if-let (accept (find current-state accept-states))
                                (progn (debug-print symbol branch (list current-state "SUCCEED2")) (values t current-state))
                                (progn (debug-print symbol branch (list current-state "FAIL2(CURRENT STATE IS NOT AN ACCEPT STATE)")) (values nil current-state)))))))
    (if (zerop (length input))
        (crawl-empty-set-paths 0 start-state 0)
        (execute 0 start-state 0))))

(defun crawl-graph (graph)
  (declare ( optimize (debug 3)) )
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
                                  collect (donuts:-> (apply #'donuts:<>2 (symbol-name vertex) (when vertex-accepted accept-state-style)) (apply #'donuts:<>2 (symbol-name end) (when end-accepted accept-state-style)) :label (format nil "~a" (if (not edge) "ℇ" edge)))))
          into nodes-and-edges
        finally (return nodes-and-edges)))

(defun fa (input expr &key print-graph optimize)
  (declare (optimize (debug 3) (safety 3)))
  (let ((regexp (notate expr)))
    (multiple-value-bind (graph accept-states) (if optimize (apply #'optimize-graph (values-list (traverse-regexp regexp 'start))) (traverse-regexp regexp 'start))
      (multiple-value-bind (accepted final-state) (execute-finite-automata input accept-states graph :debug-print print-graph)
        (when print-graph
          (format t "accepted: ~a~%graph: ~a~%accept states: ~a~%final state: ~a~%parsed: ~a~%" accepted graph accept-states final-state regexp)
          (donuts:$ (:outfile "output.dot") (donuts:& (:label (substitute #\ℇ #\# expr)) (apply #'donuts:&& (generate-donut-commands graph accept-states)))))
        accepted))))

(defparameter *decimal* "(-+#)(0+1+2+3+4+5+6+7+8+9)(0+1+2+3+4+5+6+7+8+9)*(.(0+1+2+3+4+5+6+7+8+9)*+#)")
(defparameter *decimal-test* "(-+#)(0+1)(0+1)*(.(0+1)*+#)")
