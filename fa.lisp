;; qrn75

(defpackage finite-automata
  (:use :cl))

(in-package :finite-automata)

(defun notation (exp &optional vars)
  (let (variables (num-operations 0))
    (labels ((infix-binding-power (op)
               (case op
                 (union (values 1 2))
                 (|)| (values nil nil '|)|))
                 (t (values 3 4 'concatenation))))
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
                          (multiple-value-bind (lhs-bp) (postfix-binding-power op)
                            (when lhs-bp
                              (when (< lhs-bp min-bp)
                                (loop-finish))
                              (pop exp)
                              (setf lhs (list op lhs))
                              (return-from thing)))
                          (multiple-value-bind (lhs-bp rhs-bp special) (infix-binding-power op)
                            (cond ((or (eq special '|)|) (< lhs-bp min-bp))
                                   (loop-finish))
                                  ((eq special 'concatenation)
                                   (incf num-operations)
                                   (setf op 'cat))
                                  (t
                                   (pop exp)))
                            (setf lhs (list op lhs (infix->prefix rhs-bp)))))
                     finally (return lhs)))
             (lex (exp)
               (loop for x across exp
                     append (cond ((alphanumericp x)
                                   (let ((a (read-from-string (string x))))
                                     (pushnew a variables)
                                     (list a)))
                                  (t
                                   (case x
                                     ((#\+) (prog1 '(union) (incf num-operations)))
                                     ((#\*) (prog1 '(star) (incf num-operations)))
                                     ((#\() '(|(|))
                                     ((#\)) '(|)|))
                                     ((#\space))
                                     ((#\tab))
                                     (t (error "wot in tarnation is '~a' doing here" x))))))))
      (setf exp (lex exp))
      (values (infix->prefix 0) (union vars variables) num-operations))))

(defun notate (exp &optional vars)
  (nth-value 0 (notation exp vars)))

(defun traverse-regexp (regexp vertex edge)
  (if (consp regexp)
      (case (first regexp)
        (union
         (append (traverse-regexp (second regexp) (gensym) nil) (traverse-regexp (third regexp) (gensym) nil) graph))
        (cat (let ((lhs (traverse-regexp (second regexp) (gensym) nil))
                   (rhs (traverse-regexp (third regexp) (gensym) nil)))
               ))
        (star (traverse-regexp (second regexp) (gensym) nil))
        (otherwise (error "wut in tarnation")))
      (list (list vertex regexp))))

(defun traverse-regexp (regexp vertex)
  (cond ((consp regexp)
         (case (first regexp)
           (union)
           (cat)
           (star)
           (otherwise)))
        ((symbolp regexp))
        (t nil)))



