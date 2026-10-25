;;;; radixsort.lisp — 入力しながら基数ソート(LSD, 8bit x 4パス, 安定)
;;;; 前提: types.lisp(u32 など) と fastio.lisp を先に読み込む。
;;;;
;;;; (define-radix-sort-with-read NAME &key (element-type 'u32) descending
;;;;                                       (reader 'read-fixnum) (offset 0) (head 0))
;;;;   → (NAME arr n) : 標準入力から n 個読んで arr[offset..offset+n) に入れ、
;;;;                    その範囲を整列して arr を返す。
;;;;   offset : 先頭に空ける要素数(コンパイル時の非負整数)。1 で 1-indexed。
;;;;   head   : arr[0..offset) に書く値(実行時に評価されるフォーム)。nil なら触らない。
;;;;   arr    : 長さ >= n + offset
;;;;
;;;; 例:
;;;;   (define-radix-sort-with-read sort-u32 :element-type u32)            ; 従来どおり
;;;;   (define-radix-sort-with-read sort-u32-1 :element-type u32 :offset 1) ; A[0]=0, A[1..n]
;;;;   (let ((a (make-array (1+ n) :element-type 'u32))) (sort-u32-1 a n) ...)
(declaim (optimize (speed 3) (safety 0) (debug 0)))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defun %rs-bias (element-type)
    "符号なしなら 0、符号付きなら 2^31。32bitに収まらない型はエラー。"
    (cond ((subtypep element-type '(unsigned-byte 32)) 0)
          ((subtypep element-type '(signed-byte 32)) #x80000000)
          (t (error "radix-sort: element-type ~S must fit in u32 or i32" element-type)))))

(defmacro define-radix-sort-with-read
    (name &key (element-type 'u32) descending (reader 'read-fixnum) (offset 0) (head 0))
  (unless (typep offset '(integer 0 1024))
    (error "radix-sort: offset ~S must be a small non-negative integer" offset))
  (let* ((bias (%rs-bias element-type))
         (vec  `(simple-array ,element-type (*)))
         (from-to (if descending '(from 255 downto 0) '(from 0 to 255))))
    `(defun ,name (arr n)
       (declare (optimize (speed 3) (safety 0) (debug 0))
                (type ,vec arr) (type fixnum n))
       ;; aux も同じ offset で使うので長さ n+offset(先頭は未使用)
       (let ((aux (make-array (+ n ,offset) :element-type ',element-type))
             (cnt (make-array 1024 :element-type '(unsigned-byte 32) :initial-element 0)))
         (declare (type ,vec aux) (type (simple-array (unsigned-byte 32) (1024)) cnt))
         ,@(when (and (plusp offset) head)
             `((fill arr (the ,element-type ,head) :end ,offset)))
         ;; 入力 + 4桁ぶんのヒストグラム
         (dotimes (i n)
           (let* ((val (,reader))
                  (u (logand #xffffffff (logxor val ,bias))))
             (declare (type fixnum val) (type (unsigned-byte 32) u))
             (setf (aref arr (+ i ,offset)) (the ,element-type val))
             (incf (aref cnt (logand u 255)))
             (incf (aref cnt (+ 256 (logand (ash u -8) 255))))
             (incf (aref cnt (+ 512 (logand (ash u -16) 255))))
             (incf (aref cnt (+ 768 (ash u -24))))))
         (let ((src arr) (dst aux))
           (declare (type ,vec src dst))
           ,@(loop for p from 0 below 4
                   for shift = (* 8 p)
                   collect
                   `(let ((sum ,offset) (trivial nil))   ; 書き込み位置は offset から
                      (declare (type fixnum sum))
                      (loop for k of-type fixnum ,@from-to
                            do (let ((c (aref cnt (+ ,(* 256 p) k))))
                                 (when (= c n) (setf trivial t))
                                 (setf (aref cnt (+ ,(* 256 p) k)) (the (unsigned-byte 32) sum))
                                 (setf sum (the fixnum (+ sum c)))))
                      (unless trivial
                        (dotimes (i n)
                          (let* ((val (aref src (+ i ,offset)))
                                 (u (logand #xffffffff (logxor val ,bias)))
                                 (idx (+ ,(* 256 p) (logand (ash u ,(- shift)) 255)))
                                 (pos (aref cnt idx)))
                            (declare (type (unsigned-byte 32) u pos) (type fixnum idx))
                            (setf (aref dst pos) val)
                            (setf (aref cnt idx) (the (unsigned-byte 32) (1+ pos)))))
                        (rotatef src dst))))
           ;; 結果が aux 側に残っていたら戻す(番兵部分は触らない)
           (unless (eq src arr)
             (replace arr src :start1 ,offset :start2 ,offset :end2 (+ ,offset n))))
         arr))))

(define-radix-sort-with-read sort-u32   :element-type u32)
(define-radix-sort-with-read sort-u32-1 :element-type u32 :offset 1)   ; A[0]=0