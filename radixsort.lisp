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
;;;;
;;;; (define-radix-sort NAME &key (element-type 'u32) descending)
;;;;   → (NAME arr &optional (start 0) (end (length arr)))
;;;;       手元の配列の arr[start..end) をその場で整列して arr を返す(安定)。
;;;;   定義済み: radix-sort-u32 / radix-sort-u32-desc / radix-sort-i32 / radix-sort-i32-desc
;;;;   例: (radix-sort-u32 a)  (radix-sort-u32-desc a 1)  ; 後者は 1-indexed の a[1..] を降順
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

;;; ───────── 手元の配列を基数ソート ─────────
;;;
;;; (define-radix-sort NAME &key (element-type 'u32) descending)
;;;   → (NAME arr &optional (start 0) (end (length arr)))
;;;       arr[start..end) をその場で整列して arr を返す(安定)。
;;;       start を 1 にすれば 1-indexed の配列もそのまま扱える(arr[0] は触らない)。
;;;   element-type : u32 / i32 など 32bit に収まる整数型
;;;   descending   : t なら降順
;;;
;;; 例:
;;;   (define-radix-sort radix-sort-u32      :element-type u32)
;;;   (define-radix-sort radix-sort-u32-desc :element-type u32 :descending t)
;;;   (radix-sort-u32 a)          ; a 全体を昇順
;;;   (radix-sort-u32-desc a 1)   ; a[1..] を降順(1-indexed)
(defmacro define-radix-sort (name &key (element-type 'u32) descending)
  (let* ((bias (%rs-bias element-type))
         (vec  `(simple-array ,element-type (*)))
         (from-to (if descending '(from 255 downto 0) '(from 0 to 255))))
    `(defun ,name (arr &optional (start 0) (end (length arr)))
       (declare (optimize (speed 3) (safety 0) (debug 0))
                (type ,vec arr) (type fixnum start end))
       (let ((n (- end start)))
         (declare (type fixnum n))
         (when (< n 2) (return-from ,name arr))
         ;; aux は arr と同じ添字で使うので長さ end(先頭 start 個は未使用)
         (let ((aux (make-array end :element-type ',element-type))
               (cnt (make-array 1024 :element-type '(unsigned-byte 32) :initial-element 0)))
           (declare (type ,vec aux) (type (simple-array (unsigned-byte 32) (1024)) cnt))
           ;; 4桁ぶんのヒストグラムを1回の走査で作る
           (loop for i of-type fixnum from start below end
                 do (let ((u (logand #xffffffff (logxor (aref arr i) ,bias))))
                      (declare (type (unsigned-byte 32) u))
                      (incf (aref cnt (logand u 255)))
                      (incf (aref cnt (+ 256 (logand (ash u -8) 255))))
                      (incf (aref cnt (+ 512 (logand (ash u -16) 255))))
                      (incf (aref cnt (+ 768 (ash u -24))))))
           (let ((src arr) (dst aux))
             (declare (type ,vec src dst))
             ,@(loop for p from 0 below 4
                     for shift = (* 8 p)
                     collect
                     `(let ((sum start) (trivial nil))
                        (declare (type fixnum sum))
                        ;; 度数 → 書き込み開始位置(全員同じ桁なら、このパスは省略)
                        (loop for k of-type fixnum ,@from-to
                              do (let ((c (aref cnt (+ ,(* 256 p) k))))
                                   (when (= c n) (setf trivial t))
                                   (setf (aref cnt (+ ,(* 256 p) k)) (the (unsigned-byte 32) sum))
                                   (setf sum (the fixnum (+ sum c)))))
                        (unless trivial
                          (loop for i of-type fixnum from start below end
                                do (let* ((val (aref src i))
                                          (u (logand #xffffffff (logxor val ,bias)))
                                          (idx (+ ,(* 256 p) (logand (ash u ,(- shift)) 255)))
                                          (pos (aref cnt idx)))
                                     (declare (type (unsigned-byte 32) u pos) (type fixnum idx))
                                     (setf (aref dst pos) val)
                                     (setf (aref cnt idx) (the (unsigned-byte 32) (1+ pos)))))
                          (rotatef src dst))))
             ;; 結果が aux 側に残っていたら戻す
             (unless (eq src arr)
               (replace arr src :start1 start :start2 start :end2 end))))
         arr))))

(define-radix-sort radix-sort-u32      :element-type u32)
(define-radix-sort radix-sort-u32-desc :element-type u32 :descending t)
(define-radix-sort radix-sort-i32      :element-type i32)
(define-radix-sort radix-sort-i32-desc :element-type i32 :descending t)
