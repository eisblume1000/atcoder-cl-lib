;;;; bsearch.lisp — AtCoder向け SBCL 二分探索ユーティリティ
;;;; https://github.com/eisblume1000/atcoder-cl-lib
;;;;
;;;; fastio.lisp の後ろに置いて使う(u32 などの型定義を使うため)。
;;;;
;;;; 考え方
;;;;   すべて「P が F…FT…T と並ぶとき、最初の T を探す」(めぐる式)で書いている。
;;;;   ng には P が F と確定した点、ok には T と確定した点を置き、隣り合うまで狭める。
;;;;   配列版は ng = start-1、ok = end(候補 [start,end) の両隣)から始める。
;;;;
;;;; ソート済み配列(昇順)
;;;;   (lower-bound arr x &optional start end)   arr[i] >= x となる最小の i。なければ end
;;;;   (upper-bound arr x &optional start end)   arr[i] >  x となる最小の i。なければ end
;;;;   (binary-search arr x &optional start end) arr[i] =  x となる最小の i。なければ nil
;;;;   (count-equal arr x &optional start end)   x と等しい要素の個数
;;;;   (count-range arr lo hi &optional start end)
;;;;                                             lo <= arr[i] < hi となる要素の個数
;;;;   start, end : 探す範囲 [start,end)。省略時は配列全体。1-indexed なら start = 1
;;;;
;;;;   arr の型 : (simple-array fixnum (*)) / u32 / i32 の 1 次元配列。
;;;;              同じ関数名のまま、中で型ごとの専用コードに切り替わる。
;;;;              呼び出し側で arr の型を宣言しておけば、切り替えはコンパイル時に消える。
;;;;   x, lo, hi: 常に fixnum。配列が u32 でも負の値や 2^32 以上を渡してよい
;;;;              (例: K - a が負になる場合も、そのまま渡せる)。
;;;;   返る添字 : 常に fixnum。
;;;;
;;;; 述語で二分探索(答えで二分探索)
;;;;   (bisect ok ng pred)                       P(ok)=T, P(ng)=F から始めて、T 側の境界を返す
;;;;                                             ok と ng はどちらが大きくてもよい
;;;;   (bisect-real ok ng pred &optional (iter 100))
;;;;                                             実数版。iter 回二分した後の ok を返す
;;;;   初期値は「候補の範囲のすぐ外側」に置く(T 側の外を ok、F 側の外を ng)。
;;;;
;;;; 使用例
;;;;   (lower-bound a 10)                         ; a 全体から 10 以上の最初の位置
;;;;   (binary-search a 10 1)                     ; 1-indexed の a[1..] から 10 を探す
;;;;   (count-range a 3 8)                        ; 3 <= a[i] < 8 の個数
;;;;   (bisect 1000000001 0                       ; 合計 >= K となる最小の時刻 t
;;;;           (lambda (tm) (>= (total tm) k)))
;;;;   (bisect-real n 0d0 (lambda (x) (>= (+ x (* x x x)) n)))
;;;;
;;;; 前提・制限
;;;;   - 配列は昇順にソート済みであること(検査しない)。
;;;;   - safety 0 前提で範囲検査はしない。0 <= start <= end <= (length arr) を守ること。

(declaim (optimize (speed 3) (safety 0) (debug 0)))

;; このファイル自身をコンパイルするときの note を抑える。
;; 関数単体の定義は配列の型が不明な汎用版(下の t の分岐)を含むため note が出るが、
;; 実際に使われるのは呼び出し側に inline 展開されたコードで、そちらは型に応じて最適化される。
;; (呼び出し側の note は抑えないので、型宣言漏れには気づける)
(declaim (sb-ext:muffle-conditions sb-ext:compiler-note))

;;; ───────── 内部 ─────────

;; arr の型ごとに body を複製する。各分岐の中では arr の型が確定しているので、
;; aref や比較が専用コードになる。呼び出し側で型がわかっていれば、
;; 不要な分岐はコンパイル時に消える。
(defmacro %sorted-array-case (arr &body body)
  `(typecase ,arr
     ((simple-array fixnum (*))             ,@body)
     ((simple-array (unsigned-byte 32) (*)) ,@body)
     ((simple-array (signed-byte 32) (*))   ,@body)
     (t                                     ,@body)))

;; 候補 [start,end) で、(op arr[i] x) が最初に真になる i を返す。なければ end。
;; ng = start-1, ok = end は候補の両隣に置いた番兵で、参照されることはない。
(defmacro %partition-point (arr x start end op)
  `(let ((ng (1- ,start)) (ok ,end))
     (declare (type fixnum ng ok))
     (loop while (> (- ok ng) 1)
           do (let ((mid (ash (+ ok ng) -1)))
                (declare (type fixnum mid))
                (if (,op (aref ,arr mid) ,x)
                    (setf ok mid)
                    (setf ng mid))))
     ok))

;;; ───────── ソート済み配列 ─────────

(declaim (inline lower-bound upper-bound binary-search count-equal count-range))

(defun lower-bound (arr x &optional (start 0) (end (length arr)))
  (declare (type (simple-array * (*)) arr)
           (type fixnum x start end))
  (%sorted-array-case arr
    (%partition-point arr x start end >=)))

(defun upper-bound (arr x &optional (start 0) (end (length arr)))
  (declare (type (simple-array * (*)) arr)
           (type fixnum x start end))
  (%sorted-array-case arr
    (%partition-point arr x start end >)))

(defun binary-search (arr x &optional (start 0) (end (length arr)))
  (declare (type (simple-array * (*)) arr)
           (type fixnum x start end))
  (let ((i (lower-bound arr x start end)))
    (declare (type fixnum i))
    (if (and (< i end) (= (the fixnum (aref arr i)) x))
        i
        nil)))

(defun count-equal (arr x &optional (start 0) (end (length arr)))
  (declare (type (simple-array * (*)) arr)
           (type fixnum x start end))
  (the fixnum (- (upper-bound arr x start end)
                 (lower-bound arr x start end))))

(defun count-range (arr lo hi &optional (start 0) (end (length arr)))
  (declare (type (simple-array * (*)) arr)
           (type fixnum lo hi start end))
  (if (>= lo hi)
      0
      (the fixnum (- (lower-bound arr hi start end)
                     (lower-bound arr lo start end)))))

;;; ───────── 述語で二分探索 ─────────

(declaim (inline bisect bisect-real))

(defun bisect (ok ng pred)
  (declare (type fixnum ok ng)
           (type function pred))
  (loop while (> (abs (- ok ng)) 1)
        do (let ((mid (ash (+ ok ng) -1)))
             (declare (type fixnum mid))
             (if (funcall pred mid)
                 (setf ok mid)
                 (setf ng mid))))
  ok)

(defun bisect-real (ok ng pred &optional (iter 100))
  (declare (type double-float ok ng)
           (type function pred)
           (type fixnum iter))
  (loop repeat iter
        do (let ((mid (* 0.5d0 (+ ok ng))))
             (declare (type double-float mid))
             (if (funcall pred mid)
                 (setf ok mid)
                 (setf ng mid))))
  ok)

(declaim (sb-ext:unmuffle-conditions sb-ext:compiler-note))
