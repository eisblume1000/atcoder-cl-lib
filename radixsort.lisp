;;;; radixsort.lisp — 基数ソート(LSD, 8bit ずつ, 安定)
;;;; https://github.com/eisblume1000/atcoder-cl-lib
;;;;
;;;; 前提: fastio.lisp(u32 などの型定義、read-fixnum)を先に読み込む。
;;;;
;;;; 対応する要素型と パス数
;;;;   u32 / i32 など 32bit に収まる型 … 4 パス
;;;;   fixnum / u64 / i64              … 8 パス
;;;;   (全要素で同じ桁になるパスは自動で省略する。値が小さければ実際のパスは少ない)
;;;;
;;;; ── 手元の配列を整列 ──
;;;; (define-radix-sort NAME &key (element-type 'u32) descending key-byte)
;;;;   → (NAME arr &optional (start 0) (end (length arr)))
;;;;       arr[start..end) をその場で整列して arr を返す(安定)。
;;;;   key-byte : (byte SIZE POS) を書くと、各要素のそのビット範囲だけをキーにして並べる
;;;;              (片側ソート)。キー部分は符号なし整数として比べる。
;;;;              キーが同じ要素は元の順番のまま残る(安定)。
;;;;              例: (define-radix-sort sort-by-low20 :element-type fixnum :key-byte (byte 20 0))
;;;;              パックした値を片方のフィールドで並べたいときは pack.lisp の define-pack が
;;;;              専用の関数を自動で作るので、普段はそちらを使う。
;;;;   定義済み:
;;;;     radix-sort-u32    radix-sort-u32-desc
;;;;     radix-sort-i32    radix-sort-i32-desc
;;;;     radix-sort-fixnum radix-sort-fixnum-desc
;;;;   例: (radix-sort-u32 a)  (radix-sort-fixnum-desc a 1)  ; 後者は 1-indexed の a[1..] を降順
;;;;
;;;; ── 添字の並び替え(argsort) ──
;;;; (radix-argsort keys &optional (start 0) (end (length keys)))
;;;;   → perm : keys[start..end) を昇順に並べたときの「元の添字」の列
;;;;            ((simple-array fixnum (*))、長さ end-start)。keys は書き換えない。安定。
;;;;   keys の型は fixnum / u32 / i32 のどれでもよい(中で切り替わる)。
;;;;   使いどころ: 複数の配列(並行配列)を、どれか 1 本の値の順に並べて読みたいとき
;;;;     (let ((perm (radix-argsort r)))          ; R の昇順に
;;;;       (loop for j below n
;;;;             do (let ((i (aref perm j)))
;;;;                  ... (aref l i) ... (aref r i) ...)))   ; L, R を同じ順番で読む
;;;;   降順が欲しい場合: radix-argsort-u32-desc / -i32-desc / -fixnum-desc
;;;;
;;;; ── 入力しながら整列 ──
;;;; (define-radix-sort-with-read NAME &key (element-type 'u32) descending
;;;;                                       (reader 'read-fixnum) (offset 0) (head 0))
;;;;   → (NAME arr n) : 標準入力から n 個読んで arr[offset..offset+n) に入れ、
;;;;                    その範囲を整列して arr を返す。
;;;;   offset : 先頭に空ける要素数(コンパイル時の非負整数)。1 で 1-indexed。
;;;;   head   : arr[0..offset) に書く値(実行時に評価されるフォーム)。nil なら触らない。
;;;;   arr    : 長さ >= n + offset
;;;;   例:
;;;;     (define-radix-sort-with-read sort-u32   :element-type u32)
;;;;     (define-radix-sort-with-read sort-u32-1 :element-type u32 :offset 1) ; A[0]=0, A[1..n]
;;;;     (let ((a (make-array (1+ n) :element-type 'u32))) (sort-u32-1 a n) ...)
;;;;
;;;; 仕組み
;;;;   符号付きの型は最上位ビットを反転(bias を xor)して、符号なしの順序に直してから並べる。
;;;;   ヒストグラムは全パスぶんを最初の 1 回の走査でまとめて作る。

(declaim (optimize (speed 3) (safety 0) (debug 0)))

(eval-when (:compile-toplevel :load-toplevel :execute)
  ;; 以下はマクロ展開時にだけ動く補助関数なので、速度最適化(と note)は不要
  (declaim (optimize (speed 1) (safety 1)))

  (defun %rs-spec (element-type)
    "要素型から (values bias passes) を返す。bias は符号付きのときの最上位ビット。"
    (cond ((subtypep element-type '(unsigned-byte 32)) (values 0 4))
          ((subtypep element-type '(signed-byte 32))   (values #x80000000 4))
          ((subtypep element-type '(unsigned-byte 64)) (values 0 8))
          ((subtypep element-type '(signed-byte 64))   (values #x8000000000000000 8))
          (t (error "radix-sort: element-type ~S must fit in 64 bits" element-type))))

  (defun %rs-key-plan (element-type key-byte)
    "(values key-fn passes key-type)。key-fn は値のフォームからキーのフォームを作る関数。"
    (if key-byte
        ;; (byte SIZE POS) のビット範囲だけをキーにする
        (destructuring-bind (byte-sym size pos) key-byte
          (unless (and (string= (symbol-name byte-sym) "BYTE")
                       (typep size '(integer 1 64)) (typep pos '(integer 0 63)))
            (error "radix-sort: key-byte must be (byte SIZE POS) with literal integers: ~S"
                   key-byte))
          (values (lambda (v) `(ldb (byte ,size ,pos) (ldb (byte 64 0) ,v)))
                  (ceiling size 8)
                  `(unsigned-byte ,size)))
        (multiple-value-bind (bias passes) (%rs-spec element-type)
          (values (if (= passes 4)
                      (lambda (v) `(logand #xffffffff (logxor ,v ,bias)))
                      (lambda (v) `(logxor (ldb (byte 64 0) ,v) ,bias)))
                  passes
                  `(unsigned-byte ,(* 8 passes))))))

  (defun %rs-histogram-forms (u passes)
    "キー u の各桁の度数を数えるフォームの列"
    (loop for p from 0 below passes
          collect `(incf (aref cnt (+ ,(* 256 p) (ldb (byte 8 ,(* 8 p)) ,u))))))

  (defun %rs-passes-form (src dst start end n passes from-to key-type key-fn
                          &optional comp-src comp-dst)
    "全パスぶんの並べ替えを展開する。src/dst は交互に入れ替わる。
     comp-src/comp-dst を渡すと、その配列も同じ並べ替えに付いてくる(argsort 用)。"
    (loop for p from 0 below passes
          for shift = (* 8 p)
          collect
          `(let ((sum ,start) (trivial nil))
             (declare (type fixnum sum))
             ;; 度数 → 書き込み開始位置(全員同じ桁なら、このパスは省略)
             (loop for k of-type fixnum ,@from-to
                   do (let ((c (aref cnt (+ ,(* 256 p) k))))
                        (when (= c ,n) (setf trivial t))
                        (setf (aref cnt (+ ,(* 256 p) k)) (the (unsigned-byte 32) sum))
                        (setf sum (the fixnum (+ sum c)))))
             (unless trivial
               (loop for i of-type fixnum from ,start below ,end
                     do (let* ((val (aref ,src i))
                               (u ,(funcall key-fn 'val))
                               (idx (+ ,(* 256 p) (ldb (byte 8 ,shift) u)))
                               (pos (aref cnt idx)))
                          (declare (type ,key-type u) (type fixnum idx)
                                   (type (unsigned-byte 32) pos))
                          (setf (aref ,dst pos) val)
                          ,@(when comp-src
                              `((setf (aref ,comp-dst pos) (aref ,comp-src i))))
                          (setf (aref cnt idx) (the (unsigned-byte 32) (1+ pos)))))
               (rotatef ,src ,dst)
               ,@(when comp-src `((rotatef ,comp-src ,comp-dst)))))))

  (declaim (optimize (speed 3) (safety 0) (debug 0))))

;;; ───────── 手元の配列を整列 ─────────

(defmacro define-radix-sort (name &key (element-type 'u32) descending key-byte)
  (declare (optimize (speed 1)))           ; マクロ本体(展開処理)の note を抑える
  (multiple-value-bind (key-fn passes key-type) (%rs-key-plan element-type key-byte)
    (let ((vec     `(simple-array ,element-type (*)))
          (from-to (if descending '(from 255 downto 0) '(from 0 to 255))))
      `(defun ,name (arr &optional (start 0) (end (length arr)))
         (declare (optimize (speed 3) (safety 0) (debug 0))
                  (type ,vec arr) (type fixnum start end))
         (let ((n (- end start)))
           (declare (type fixnum n))
           (when (< n 2) (return-from ,name arr))
           ;; aux は arr と同じ添字で使うので長さ end(先頭 start 個は未使用)
           (let ((aux (make-array end :element-type ',element-type))
                 (cnt (make-array ,(* 256 passes) :element-type '(unsigned-byte 32)
                                                  :initial-element 0)))
             (declare (type ,vec aux)
                      (type (simple-array (unsigned-byte 32) (,(* 256 passes))) cnt))
             ;; 全パスぶんのヒストグラムを 1 回の走査で作る
             (loop for i of-type fixnum from start below end
                   do (let ((u ,(funcall key-fn '(aref arr i))))
                        (declare (type ,key-type u))
                        ,@(%rs-histogram-forms 'u passes)))
             (let ((src arr) (dst aux))
               (declare (type ,vec src dst))
               ,@(%rs-passes-form 'src 'dst 'start 'end 'n passes from-to key-type key-fn)
               ;; 結果が aux 側に残っていたら戻す
               (unless (eq src arr)
                 (replace arr src :start1 start :start2 start :end2 end))))
           arr)))))

;;; ───────── argsort ─────────

;; キーのコピーと添字の配列を一緒に並べ替える。どちらも先頭から順に読み書きするので、
;; 「添字を並べ替えながら毎回 keys[idx] を引く」方式よりキャッシュ効率が良い。
(defmacro define-radix-argsort (name &key (element-type 'u32) descending)
  (declare (optimize (speed 1)))
  (multiple-value-bind (key-fn passes key-type) (%rs-key-plan element-type nil)
    (let ((vec     `(simple-array ,element-type (*)))
          (from-to (if descending '(from 255 downto 0) '(from 0 to 255))))
      `(defun ,name (keys &optional (start 0) (end (length keys)))
         (declare (optimize (speed 3) (safety 0) (debug 0))
                  (type ,vec keys) (type fixnum start end))
         (let* ((n (max 0 (- end start)))
                (kbuf (subseq keys start (+ start n)))
                (kaux (make-array n :element-type ',element-type))
                (perm (make-array n :element-type 'fixnum))
                (paux (make-array n :element-type 'fixnum))
                (cnt (make-array ,(* 256 passes) :element-type '(unsigned-byte 32)
                                                 :initial-element 0)))
           (declare (type fixnum n) (type ,vec kbuf kaux)
                    (type (simple-array fixnum (*)) perm paux)
                    (type (simple-array (unsigned-byte 32) (,(* 256 passes))) cnt))
           (dotimes (i n)
             (setf (aref perm i) (+ start i))
             (let ((u ,(funcall key-fn '(aref kbuf i))))
               (declare (type ,key-type u))
               ,@(%rs-histogram-forms 'u passes)))
           (when (>= n 2)
             (let ((src kbuf) (dst kaux) (psrc perm) (pdst paux) (s 0))
               (declare (type ,vec src dst) (type (simple-array fixnum (*)) psrc pdst)
                        (type fixnum s))
               ,@(%rs-passes-form 'src 'dst 's 'n 'n passes from-to key-type key-fn
                                  'psrc 'pdst)
               (setf perm psrc)))
           perm)))))

(define-radix-argsort radix-argsort-u32         :element-type u32)
(define-radix-argsort radix-argsort-u32-desc    :element-type u32 :descending t)
(define-radix-argsort radix-argsort-i32         :element-type i32)
(define-radix-argsort radix-argsort-i32-desc    :element-type i32 :descending t)
(define-radix-argsort radix-argsort-fixnum      :element-type fixnum)
(define-radix-argsort radix-argsort-fixnum-desc :element-type fixnum :descending t)

(declaim (inline radix-argsort))
(defun radix-argsort (keys &optional (start 0) (end (length keys)))
  "keys の型に合わせて radix-argsort-u32 / -i32 / -fixnum を呼ぶ(昇順)"
  (declare (type (simple-array * (*)) keys) (type fixnum start end))
  (etypecase keys
    ((simple-array (unsigned-byte 32) (*)) (radix-argsort-u32 keys start end))
    ((simple-array (signed-byte 32) (*))   (radix-argsort-i32 keys start end))
    ((simple-array fixnum (*))             (radix-argsort-fixnum keys start end))))

;;; ───────── 入力しながら整列 ─────────

(defmacro define-radix-sort-with-read
    (name &key (element-type 'u32) descending (reader 'read-fixnum) (offset 0) (head 0))
  (declare (optimize (speed 1)))
  (unless (typep offset '(integer 0 1024))
    (error "radix-sort: offset ~S must be a small non-negative integer" offset))
  (multiple-value-bind (key-fn passes key-type) (%rs-key-plan element-type nil)
    (let ((vec     `(simple-array ,element-type (*)))
          (from-to (if descending '(from 255 downto 0) '(from 0 to 255))))
      `(defun ,name (arr n)
         (declare (optimize (speed 3) (safety 0) (debug 0))
                  (type ,vec arr) (type fixnum n))
         (let ((start ,offset)
               (end (+ n ,offset))
               ;; aux も同じ添字で使うので長さ n+offset(先頭は未使用)
               (aux (make-array (+ n ,offset) :element-type ',element-type))
               (cnt (make-array ,(* 256 passes) :element-type '(unsigned-byte 32)
                                                :initial-element 0)))
           (declare (type fixnum start end) (type ,vec aux)
                    (type (simple-array (unsigned-byte 32) (,(* 256 passes))) cnt))
           ,@(when (and (plusp offset) head)
               `((fill arr (the ,element-type ,head) :end ,offset)))
           ;; 入力 + 全パスぶんのヒストグラム
           (loop for i of-type fixnum from start below end
                 do (let* ((val (,reader))
                           (u ,(funcall key-fn 'val)))
                      (declare (type fixnum val) (type ,key-type u))
                      (setf (aref arr i) (the ,element-type val))
                      ,@(%rs-histogram-forms 'u passes)))
           (when (>= n 2)
             (let ((src arr) (dst aux))
               (declare (type ,vec src dst))
               ,@(%rs-passes-form 'src 'dst 'start 'end 'n passes from-to key-type key-fn)
               ;; 結果が aux 側に残っていたら戻す(番兵部分は触らない)
               (unless (eq src arr)
                 (replace arr src :start1 start :start2 start :end2 end))))
           arr)))))

;;; ───────── 定義済み ─────────

(define-radix-sort radix-sort-u32         :element-type u32)
(define-radix-sort radix-sort-u32-desc    :element-type u32 :descending t)
(define-radix-sort radix-sort-i32         :element-type i32)
(define-radix-sort radix-sort-i32-desc    :element-type i32 :descending t)
(define-radix-sort radix-sort-fixnum      :element-type fixnum)
(define-radix-sort radix-sort-fixnum-desc :element-type fixnum :descending t)

(define-radix-sort-with-read sort-u32   :element-type u32)
(define-radix-sort-with-read sort-u32-1 :element-type u32 :offset 1)   ; A[0]=0
